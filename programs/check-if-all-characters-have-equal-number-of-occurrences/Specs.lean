import Aegis.AreOccurrencesEqual.Code.Funs

/-!
# Specifications of `Aegis.AreOccurrencesEqual.are_occurrences_equal`

LeetCode problem `check-if-all-characters-have-equal-number-of-occurrences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.AreOccurrencesEqual

  namespace AegisSpec.AreOccurrencesEqual

  def occ (s : Slice Std.U8) (c : ℕ) : ℕ :=
    (s.val.filter (fun b => b.val = c)).length

  def AllFreqEqual (s : Slice Std.U8) : Prop :=
    ∀ c d : ℕ, c ≤ 255 → d ≤ 255 → 0 < occ s c → 0 < occ s d → occ s c = occ s d

  def numOccurring (s : Slice Std.U8) : ℕ :=
    ((Finset.range 256).filter (fun c => 0 < occ s c)).card

  /-- Let occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c. Whenever the function returns a result r, r = true if and only if for every two byte values c and d with 0 <= c,d <= 255, if occ(c) > 0 and occ(d) > 0 then occ(c) = occ(d). Equivalently, all characters that appear in s have the same number of occurrences. Also r = false if and only if this condition does not hold.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_1
      (s : Slice Std.U8)
      (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
      (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
      (r : Bool) (hres : are_occurrences_equal s = Result.ok r) :
      (r = true ↔ AllFreqEqual s) ∧ (r = false ↔ ¬ AllFreqEqual s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
        (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
        (r : Bool) (hres : are_occurrences_equal s = Result.ok r), (r = true ↔ AllFreqEqual s) ∧ (r = false ↔ ¬ AllFreqEqual s)) := by
    sorry

  /-- The function does not fail on any input satisfying the preconditions: for every such s, there exists a Boolean r such that are_occurrences_equal s = Result.ok r. Moreover, for every byte value c, letting occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c, we have 0 <= occ(c) <= len(s) <= 1000, so occurrence counts are bounded and fit in 64-bit integers.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2
      (s : Slice Std.U8)
      (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
      (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122) :
      (∃ r : Bool, are_occurrences_equal s = Result.ok r) ∧
        (∀ c : ℕ, occ s c ≤ (Slice.len s).val) ∧
        (∀ c : ℕ, occ s c ≤ 1000) ∧
        (Slice.len s).val ≤ 1000 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
        (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122), (∃ r : Bool, are_occurrences_equal s = Result.ok r) ∧
          (∀ c : ℕ, occ s c ≤ (Slice.len s).val) ∧
          (∀ c : ℕ, occ s c ≤ 1000) ∧
          (Slice.len s).val ≤ 1000) := by
    sorry

  /-- Let occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c. Whenever the function returns r = true, for every index i with 0 <= i < len(s), occ(s[i]) = occ(s[0]). In particular, the character at index 0 is a witness whose frequency is the common frequency.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3
      (s : Slice Std.U8)
      (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
      (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
      (hres : are_occurrences_equal s = Result.ok true) :
      ∀ (i : ℕ) (h : i < (Slice.len s).val),
        occ s ((s.val[i]'h).val) =
          occ s ((s.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen_lb)).val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
        (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
        (hres : are_occurrences_equal s = Result.ok true), ∀ (i : ℕ) (h : i < (Slice.len s).val),
          occ s ((s.val[i]'h).val) =
            occ s ((s.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen_lb)).val)) := by
    sorry

  /-- Let occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c. Whenever the function returns r = false, there exist byte values a and b with 0 <= a,b <= 255 such that a != b, occ(a) > 0, occ(b) > 0, and occ(a) != occ(b). Thus a false answer has a concrete pair of appearing characters with different frequencies.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4
      (s : Slice Std.U8)
      (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
      (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
      (hres : are_occurrences_equal s = Result.ok false) :
      ∃ a b : ℕ, a ≤ 255 ∧ b ≤ 255 ∧ a ≠ b ∧ 0 < occ s a ∧ 0 < occ s b ∧
        occ s a ≠ occ s b := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
        (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
        (hres : are_occurrences_equal s = Result.ok false), ∃ a b : ℕ, a ≤ 255 ∧ b ≤ 255 ∧ a ≠ b ∧ 0 < occ s a ∧ 0 < occ s b ∧
          occ s a ≠ occ s b) := by
    sorry

  /-- Let occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c. Whenever the function returns r = true, let m be the number of byte values c with occ(c) > 0, and let k be the common occurrence count, so every such c has occ(c) = k. Then m >= 1, k >= 1, and len(s) = m * k. Consequently, both m and k divide len(s).
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5
      (s : Slice Std.U8)
      (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
      (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
      (hres : are_occurrences_equal s = Result.ok true) :
      ∃ k : ℕ, 1 ≤ k ∧
        (∀ c : ℕ, c ≤ 255 → 0 < occ s c → occ s c = k) ∧
        1 ≤ numOccurring s ∧
        (Slice.len s).val = numOccurring s * k ∧
        numOccurring s ∣ (Slice.len s).val ∧ k ∣ (Slice.len s).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
        (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
        (hres : are_occurrences_equal s = Result.ok true), ∃ k : ℕ, 1 ≤ k ∧
          (∀ c : ℕ, c ≤ 255 → 0 < occ s c → occ s c = k) ∧
          1 ≤ numOccurring s ∧
          (Slice.len s).val = numOccurring s * k ∧
          numOccurring s ∣ (Slice.len s).val ∧ k ∣ (Slice.len s).val) := by
    sorry

  /-- For any such s and t, the function returns results r_s on s and r_t on t, and r_s = r_t. Thus the answer depends only on the multiset of characters, not on their order.
    Preconditions: s and t are byte slices with 1 <= len(s) <= 1000 and 1 <= len(t) <= 1000, all entries of s and t are lowercase English letters (97 <= byte <= 122), len(s) = len(t), and for every byte value c, occ_s(c) = occ_t(c), where occ_s(c) counts indices i with s[i] = c and occ_t(c) counts indices i with t[i] = c. -/
  theorem spec_6
      (s t : Slice Std.U8)
      (hs_lb : 1 ≤ (Slice.len s).val) (hs_ub : (Slice.len s).val ≤ 1000)
      (ht_lb : 1 ≤ (Slice.len t).val) (ht_ub : (Slice.len t).val ≤ 1000)
      (hs_bytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
      (ht_bytes : ∀ (i : ℕ) (h : i < (Slice.len t).val),
        97 ≤ (t.val[i]'h).val ∧ (t.val[i]'h).val ≤ 122)
      (hlen : (Slice.len s).val = (Slice.len t).val)
      (hocc : ∀ c : ℕ, c ≤ 255 → occ s c = occ t c) :
      ∃ rs rt : Bool,
        are_occurrences_equal s = Result.ok rs ∧ are_occurrences_equal t = Result.ok rt ∧
          rs = rt := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_lb : 1 ≤ (Slice.len s).val) (hs_ub : (Slice.len s).val ≤ 1000)
        (ht_lb : 1 ≤ (Slice.len t).val) (ht_ub : (Slice.len t).val ≤ 1000)
        (hs_bytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
        (ht_bytes : ∀ (i : ℕ) (h : i < (Slice.len t).val),
          97 ≤ (t.val[i]'h).val ∧ (t.val[i]'h).val ≤ 122)
        (hlen : (Slice.len s).val = (Slice.len t).val)
        (hocc : ∀ c : ℕ, c ≤ 255 → occ s c = occ t c), ∃ rs rt : Bool,
          are_occurrences_equal s = Result.ok rs ∧ are_occurrences_equal t = Result.ok rt ∧
            rs = rt) := by
    sorry

  /-- Let occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c. Whenever the function returns r = false, there exists an index i with 0 <= i < len(s) such that occ(s[i]) != occ(s[0]).
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_7
      (s : Slice Std.U8)
      (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
      (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
        97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
      (hres : are_occurrences_equal s = Result.ok false) :
      ∃ (i : ℕ) (h : i < (Slice.len s).val),
        occ s ((s.val[i]'h).val) ≠
          occ s ((s.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen_lb)).val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lb : 1 ≤ (Slice.len s).val) (hlen_ub : (Slice.len s).val ≤ 1000)
        (hbytes : ∀ (i : ℕ) (h : i < (Slice.len s).val),
          97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
        (hres : are_occurrences_equal s = Result.ok false), ∃ (i : ℕ) (h : i < (Slice.len s).val),
          occ s ((s.val[i]'h).val) ≠
            occ s ((s.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen_lb)).val)) := by
    sorry

  end AegisSpec.AreOccurrencesEqual
