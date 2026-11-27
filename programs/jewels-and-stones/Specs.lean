import Aegis.NumJewelsInStones.Code.Funs

/-!
# Specifications of `Aegis.NumJewelsInStones.num_jewels_in_stones`

LeetCode problem `jewels-and-stones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumJewelsInStones

def isLetter (b : Std.U8) : Prop := (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122)

def occurs (b : Std.U8) (s : Slice Std.U8) : Prop := ∃ j : Fin s.val.length, s.val.get j = b

noncomputable def countJewels (jewels stones : Slice Std.U8) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin stones.val.length =>
    occurs (stones.val.get i) jewels)).card

noncomputable def countByte (stones : Slice Std.U8) (b : Std.U8) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin stones.val.length =>
    stones.val.get i = b)).card

def eraseAt (l : List Std.U8) (p : ℕ) : List Std.U8 := l.take p ++ l.drop (p + 1)

def insertAt (l : List Std.U8) (p : ℕ) (b : Std.U8) : List Std.U8 :=
  l.take p ++ b :: l.drop p

/-- The function returns a result r and r equals the number of indices i with 0 <= i < len(stones) such that stones[i] occurs in jewels, where a byte b occurs in jewels means there exists j with 0 <= j < len(jewels) and jewels[j] = b. Equivalently, r is the sum over all i with 0 <= i < len(stones) of 1 if stones[i] is in the set of bytes of jewels, and 0 otherwise. Byte comparison is exact, so letters are case-sensitive.
  Preconditions: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte of jewels and of stones is an English letter (ASCII 65..90 or 97..122); and the bytes of jewels are pairwise distinct. -/
theorem spec_1 (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup) :
    ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        r.val = (countJewels jewels stones : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup), ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        r.val = (countJewels jewels stones : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, 0 <= r <= len(stones).
  Preconditions: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte of jewels and of stones is an English letter (ASCII 65..90 or 97..122); and the bytes of jewels are pairwise distinct. -/
theorem spec_2 (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup) :
    ∀ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r →
        0 ≤ r.val ∧ r.val ≤ (stones.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup), ∀ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r →
        0 ≤ r.val ∧ r.val ≤ (stones.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte of jewels and of stones is an English letter (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct; and for every i with 0 <= i < len(stones), stones[i] does not occur in jewels, where b occurs in jewels means there exists j with 0 <= j < len(jewels) and jewels[j] = b. -/
theorem spec_3 (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (h_all_missing : ∀ i : Fin stones.val.length, ¬ occurs (stones.val.get i) jewels) :
    ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧ r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (h_all_missing : ∀ i : Fin stones.val.length, ¬ occurs (stones.val.get i) jewels), ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = len(stones).
  Preconditions: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte of jewels and of stones is an English letter (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct; and for every i with 0 <= i < len(stones), stones[i] occurs in jewels, where b occurs in jewels means there exists j with 0 <= j < len(jewels) and jewels[j] = b. -/
theorem spec_4 (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (h_all_jewels : ∀ i : Fin stones.val.length, occurs (stones.val.get i) jewels) :
    ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        r.val = (stones.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (h_all_jewels : ∀ i : Fin stones.val.length, occurs (stones.val.get i) jewels), ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        r.val = (stones.val.length : ℤ)) := by
  sorry

/-- The function does not fail: for every such input it returns a result r, with no panic, no out-of-bounds access, and no i64 overflow.
  Preconditions: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte of jewels and of stones is an English letter (ASCII 65..90 or 97..122); and the bytes of jewels are pairwise distinct. -/
theorem spec_5 (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup) :
    ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (jewels stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup), ∃ r : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r) := by
  sorry

/-- The calls on (jewels, stones1) and (jewels, stones2) both return results r1 and r2, and r1 = r2.
  Preconditions: jewels, stones1, and stones2 satisfy the common constraints: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones1) <= 50; 0 <= len(stones2) <= 50; all bytes are English letters (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct. Also len(stones1) = len(stones2), and for every byte b, the number of indices i with stones1[i] = b equals the number of indices i with stones2[i] = b. -/
theorem spec_6 (jewels stones1 stones2 : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs1_len_le50 : stones1.val.length ≤ 50)
    (hs2_len_le50 : stones2.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs1_letters : ∀ b ∈ stones1.val, isLetter b)
    (hs2_letters : ∀ b ∈ stones2.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (h_len : stones1.val.length = stones2.val.length)
    (h_count : ∀ b : Std.U8, countByte stones1 b = countByte stones2 b) :
    ∃ r1 r2 : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones1 = ok r1 ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones2 = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (jewels stones1 stones2 : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs1_len_le50 : stones1.val.length ≤ 50)
    (hs2_len_le50 : stones2.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs1_letters : ∀ b ∈ stones1.val, isLetter b)
    (hs2_letters : ∀ b ∈ stones2.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (h_len : stones1.val.length = stones2.val.length)
    (h_count : ∀ b : Std.U8, countByte stones1 b = countByte stones2 b), ∃ r1 r2 : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones1 = ok r1 ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones2 = ok r2 ∧ r1 = r2) := by
  sorry

/-- The calls on (jewels1, stones) and (jewels2, stones) both return results r1 and r2, and r1 = r2.
  Preconditions: jewels1, jewels2, and stones satisfy the common constraints: len(jewels1) >= 1; len(jewels2) >= 1; len(jewels1) <= 50; len(jewels2) <= 50; 0 <= len(stones) <= 50; all bytes are English letters (ASCII 65..90 or 97..122); the bytes of jewels1 are pairwise distinct; the bytes of jewels2 are pairwise distinct. Also len(jewels1) = len(jewels2), and for every byte b, b occurs in jewels1 iff b occurs in jewels2, where occurs means there exists j with 0 <= j < len(jewels1) and jewels1[j] = b, respectively j < len(jewels2) and jewels2[j] = b. -/
theorem spec_7 (jewels1 jewels2 stones : Slice Std.U8)
    (hj1_len_ge1 : 1 ≤ jewels1.val.length)
    (hj2_len_ge1 : 1 ≤ jewels2.val.length)
    (hj1_len_le50 : jewels1.val.length ≤ 50)
    (hj2_len_le50 : jewels2.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj1_letters : ∀ b ∈ jewels1.val, isLetter b)
    (hj2_letters : ∀ b ∈ jewels2.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj1_nodup : jewels1.val.Nodup)
    (hj2_nodup : jewels2.val.Nodup)
    (h_len : jewels1.val.length = jewels2.val.length)
    (h_occ : ∀ b : Std.U8, occurs b jewels1 ↔ occurs b jewels2) :
    ∃ r1 r2 : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels1 stones = ok r1 ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels2 stones = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (jewels1 jewels2 stones : Slice Std.U8)
    (hj1_len_ge1 : 1 ≤ jewels1.val.length)
    (hj2_len_ge1 : 1 ≤ jewels2.val.length)
    (hj1_len_le50 : jewels1.val.length ≤ 50)
    (hj2_len_le50 : jewels2.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj1_letters : ∀ b ∈ jewels1.val, isLetter b)
    (hj2_letters : ∀ b ∈ jewels2.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj1_nodup : jewels1.val.Nodup)
    (hj2_nodup : jewels2.val.Nodup)
    (h_len : jewels1.val.length = jewels2.val.length)
    (h_occ : ∀ b : Std.U8, occurs b jewels1 ↔ occurs b jewels2), ∃ r1 r2 : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels1 stones = ok r1 ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels2 stones = ok r2 ∧ r1 = r2) := by
  sorry

/-- The calls on (jewels, stones) and (jewels, stones') both return results r and r', and r = r'.
  Preconditions: jewels and stones satisfy the common constraints: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte is an English letter (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct. Let p be an index with 0 <= p < len(stones), and suppose stones[p] does not occur in jewels. Let stones' be the sequence of length len(stones)-1 with stones'[i] = stones[i] for 0 <= i < p and stones'[i] = stones[i+1] for p <= i < len(stones)-1. -/
theorem spec_8 (jewels stones stones' : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (p : ℕ)
    (hp : p < stones.val.length)
    (h_missing : ¬ occurs (stones.val.get ⟨p, hp⟩) jewels)
    (h_stones' : stones'.val = eraseAt stones.val p) :
    ∃ r r' : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones' = ok r' ∧ r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (jewels stones stones' : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (p : ℕ)
    (hp : p < stones.val.length)
    (h_missing : ¬ occurs (stones.val.get ⟨p, hp⟩) jewels)
    (h_stones' : stones'.val = eraseAt stones.val p), ∃ r r' : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones' = ok r' ∧ r = r') := by
  sorry

/-- The calls on (jewels, stones) and (jewels, stones') both return results r and r', and r' = r + 1.
  Preconditions: jewels and stones satisfy the common constraints: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte is an English letter (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct. Let b be a byte that occurs in jewels. Let p be an integer with 0 <= p <= len(stones), and assume len(stones) < 50. Let stones' be the sequence of length len(stones)+1 obtained by inserting b at position p: stones'[i] = stones[i] for 0 <= i < p, stones'[p] = b, and stones'[i] = stones[i-1] for p < i <= len(stones). -/
theorem spec_9 (jewels stones stones' : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (b : Std.U8)
    (hb : occurs b jewels)
    (p : ℕ)
    (hp : p ≤ stones.val.length)
    (hs_len_lt50 : stones.val.length < 50)
    (h_stones' : stones'.val = insertAt stones.val p b) :
    ∃ r r' : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones' = ok r' ∧
          r'.val = r.val + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (jewels stones stones' : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (b : Std.U8)
    (hb : occurs b jewels)
    (p : ℕ)
    (hp : p ≤ stones.val.length)
    (hs_len_lt50 : stones.val.length < 50)
    (h_stones' : stones'.val = insertAt stones.val p b), ∃ r r' : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones' = ok r' ∧
          r'.val = r.val + 1) := by
  sorry

/-- The calls on (jewels, stones), (jewels, stonesL), and (jewels, stonesR) all return results r, rL, and rR, and r = rL + rR.
  Preconditions: jewels and stones satisfy the common constraints: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte is an English letter (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct. Let k be an integer with 0 <= k <= len(stones). Let stonesL be stones[0..k) (length k), and let stonesR be stones[k..len(stones)) (length len(stones)-k). -/
theorem spec_10 (jewels stones stonesL stonesR : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (k : ℕ)
    (hk : k ≤ stones.val.length)
    (hL : stonesL.val = stones.val.take k)
    (hR : stonesR.val = stones.val.drop k) :
    ∃ r rL rR : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stonesL = ok rL ∧
          Aegis.NumJewelsInStones.num_jewels_in_stones jewels stonesR = ok rR ∧
            r.val = rL.val + rR.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (jewels stones stonesL stonesR : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (k : ℕ)
    (hk : k ≤ stones.val.length)
    (hL : stonesL.val = stones.val.take k)
    (hR : stonesR.val = stones.val.drop k), ∃ r rL rR : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels stonesL = ok rL ∧
          Aegis.NumJewelsInStones.num_jewels_in_stones jewels stonesR = ok rR ∧
            r.val = rL.val + rR.val) := by
  sorry

/-- The calls on (jewels, stones) and (jewels', stones) both return results r and r'. Let N be the number of indices i with 0 <= i < len(stones) and stones[i] = c. Then r' = r + N.
  Preconditions: jewels and stones satisfy the common constraints: len(jewels) >= 1; len(jewels) <= 50; 0 <= len(stones) <= 50; every byte is an English letter (ASCII 65..90 or 97..122); the bytes of jewels are pairwise distinct. Let c be an English letter that does not occur in jewels, and assume len(jewels) < 50. Let jewels' be obtained by appending c to jewels: len(jewels') = len(jewels)+1, jewels'[i] = jewels[i] for 0 <= i < len(jewels), and jewels'[len(jewels)] = c. -/
theorem spec_11 (jewels jewels' stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (c : Std.U8)
    (hc_letter : isLetter c)
    (hc_not_jewel : ¬ occurs c jewels)
    (hj_len_lt50 : jewels.val.length < 50)
    (h_jewels' : jewels'.val = jewels.val ++ [c]) :
    ∃ r r' : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels' stones = ok r' ∧
          r'.val = r.val + (countByte stones c : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (jewels jewels' stones : Slice Std.U8)
    (hj_len_ge1 : 1 ≤ jewels.val.length)
    (hj_len_le50 : jewels.val.length ≤ 50)
    (hs_len_le50 : stones.val.length ≤ 50)
    (hj_letters : ∀ b ∈ jewels.val, isLetter b)
    (hs_letters : ∀ b ∈ stones.val, isLetter b)
    (hj_nodup : jewels.val.Nodup)
    (c : Std.U8)
    (hc_letter : isLetter c)
    (hc_not_jewel : ¬ occurs c jewels)
    (hj_len_lt50 : jewels.val.length < 50)
    (h_jewels' : jewels'.val = jewels.val ++ [c]), ∃ r r' : Std.I64,
      Aegis.NumJewelsInStones.num_jewels_in_stones jewels stones = ok r ∧
        Aegis.NumJewelsInStones.num_jewels_in_stones jewels' stones = ok r' ∧
          r'.val = r.val + (countByte stones c : ℤ)) := by
  sorry

end AegisSpec.NumJewelsInStones
