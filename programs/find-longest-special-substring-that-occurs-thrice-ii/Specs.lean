import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-longest-special-substring-that-occurs-thrice-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumLength

  open Aegis.MaximumLength

  def Occ (s : Slice Std.U8) (c : Std.U8) (L : ℤ) : ℤ :=
    if 1 ≤ L ∧ L ≤ (s.val.length : ℤ) then
      (((List.range (s.val.length + 1)).filter
        (fun (a : ℕ) => decide ((a : ℤ) + L ≤ (s.val.length : ℤ) ∧
          ∀ k : ℕ, k < L.toNat → s.val[a + k]? = some c))).length : ℤ)
    else 0

  def byteCount (s : Slice Std.U8) (c : Std.U8) : ℤ := Occ s c 1

  def runFrom (s : Slice Std.U8) (a : ℕ) : ℕ :=
    ((List.range (s.val.length - a)).takeWhile (fun k => s.val[a + k]? = s.val[a]?)).length

  def maxRun (s : Slice Std.U8) : ℤ :=
    (((List.range s.val.length).map (runFrom s)).foldr max 0 : ℤ)

  /-- The function returns a result r and the following holds. Define Occ(c,L), for a byte c and an integer L with 1 <= L <= len(s), as the number of indices i such that 0 <= i <= len(s)-L and s[i+k]=c for every k with 0 <= k < L. If there exist a byte c and an integer L with 1 <= L <= len(s) and Occ(c,L) >= 3, then r is the largest such L: r >= 1, Occ(c,r) >= 3 for at least one byte c, and for every byte c' and every integer L with r < L <= len(s), Occ(c',L) <= 2. If no such pair (c,L) exists, then r = -1.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s consists only of lowercase ASCII letters). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, maximum_length s = ok r ∧
        ((∃ (c : Std.U8) (L : ℤ), 1 ≤ L ∧ L ≤ (s.val.length : ℤ) ∧ 3 ≤ Occ s c L) →
          (1 ≤ r.val ∧ (∃ c : Std.U8, 3 ≤ Occ s c r.val) ∧
            (∀ (c' : Std.U8) (L : ℤ),
              r.val < L → L ≤ (s.val.length : ℤ) → Occ s c' L ≤ 2))) ∧
        ((¬ ∃ (c : Std.U8) (L : ℤ), 1 ≤ L ∧ L ≤ (s.val.length : ℤ) ∧ 3 ≤ Occ s c L) →
          r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, maximum_length s = ok r ∧
          ((∃ (c : Std.U8) (L : ℤ), 1 ≤ L ∧ L ≤ (s.val.length : ℤ) ∧ 3 ≤ Occ s c L) →
            (1 ≤ r.val ∧ (∃ c : Std.U8, 3 ≤ Occ s c r.val) ∧
              (∀ (c' : Std.U8) (L : ℤ),
                r.val < L → L ≤ (s.val.length : ℤ) → Occ s c' L ≤ 2))) ∧
          ((¬ ∃ (c : Std.U8) (L : ℤ), 1 ≤ L ∧ L ≤ (s.val.length : ℤ) ∧ 3 ≤ Occ s c L) →
            r.val = -1)) := by
    sorry

  /-- For every s satisfying the preconditions, maximum_length(s) returns a result r; in particular, it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, maximum_length s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, maximum_length s = ok r) := by
    sorry

  /-- Whenever maximum_length(s) returns a result r, either r = -1 or 1 <= r <= len(s).
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r →
        (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ))) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r →
          (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)))) := by
    sorry

  /-- Whenever maximum_length(s) returns a result r with r >= 1, there exists a byte c such that Occ(c,r) >= 3, where Occ(c,r) is the number of indices i with 0 <= i <= len(s)-r and s[i+k]=c for all k with 0 <= k < r.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
        ∃ c : Std.U8, 3 ≤ Occ s c r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
          ∃ c : Std.U8, 3 ≤ Occ s c r.val) := by
    sorry

  /-- Whenever maximum_length(s) returns a result r with r >= 1, for every byte c and every integer L with r < L <= len(s), Occ(c,L) <= 2, where Occ(c,L) is the number of indices i with 0 <= i <= len(s)-L and s[i+k]=c for all k with 0 <= k < L.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
        ∀ (c : Std.U8) (L : ℤ), r.val < L → L ≤ (s.val.length : ℤ) → Occ s c L ≤ 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
          ∀ (c : Std.U8) (L : ℤ), r.val < L → L ≤ (s.val.length : ℤ) → Occ s c L ≤ 2) := by
    sorry

  /-- Whenever maximum_length(s) returns a result r, r = -1 if and only if for every byte c, the number of indices i with 0 <= i < len(s) and s[i]=c is at most 2.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r →
        (r.val = -1 ↔ ∀ c : Std.U8, byteCount s c ≤ 2) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r →
          (r.val = -1 ↔ ∀ c : Std.U8, byteCount s c ≤ 2)) := by
    sorry

  /-- The function returns the result len(s)-2.
    Preconditions: 3 <= len(s) <= 500000, all bytes of s are lowercase ASCII letters (97 <= s[i] <= 122 for every 0 <= i < len(s)), and all bytes of s are equal (s[i]=s[0] for every i with 0 <= i < len(s)). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hconst : ∀ i : ℕ, i < s.val.length → s.val[i]? = s.val[0]?) :
      ∃ r : Std.I64, maximum_length s = ok r ∧ r.val = (s.val.length : ℤ) - 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hconst : ∀ i : ℕ, i < s.val.length → s.val[i]? = s.val[0]?), ∃ r : Std.I64, maximum_length s = ok r ∧ r.val = (s.val.length : ℤ) - 2) := by
    sorry

  /-- If s[0]=s[1] and s[1]=s[2], the function returns 1; otherwise it returns -1.
    Preconditions: 3 <= len(s) <= 500000, all bytes of s are lowercase ASCII letters, and len(s)=3. -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hlen : s.val.length = 3) :
      ∃ r : Std.I64, maximum_length s = ok r ∧
        ((s.val[0]? = s.val[1]? ∧ s.val[1]? = s.val[2]?) → r.val = 1) ∧
        (¬ (s.val[0]? = s.val[1]? ∧ s.val[1]? = s.val[2]?) → r.val = -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hlen : s.val.length = 3), ∃ r : Std.I64, maximum_length s = ok r ∧
          ((s.val[0]? = s.val[1]? ∧ s.val[1]? = s.val[2]?) → r.val = 1) ∧
          (¬ (s.val[0]? = s.val[1]? ∧ s.val[1]? = s.val[2]?) → r.val = -1)) := by
    sorry

  /-- Let M be the maximum length of a contiguous block of equal bytes in s, that is, M = max{ b-a+1 : 0 <= a <= b < len(s) and s[k]=s[a] for every k with a <= k <= b }. Whenever maximum_length(s) returns a result r with r >= 1, r <= M.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val → r.val ≤ maxRun s := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val → r.val ≤ maxRun s) := by
    sorry

  /-- Whenever maximum_length(s) returns a result r with r >= 1, there exists a byte c such that the number of indices i with 0 <= i < len(s) and s[i]=c is at least r+2.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
        ∃ c : Std.U8, r.val + 2 ≤ byteCount s c := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
          ∃ c : Std.U8, r.val + 2 ≤ byteCount s c) := by
    sorry

  /-- Whenever maximum_length(s) returns a and maximum_length(t) returns b, we have b >= a, treating -1 as an integer less than every positive result.
    Preconditions: Both s and t satisfy: 3 <= len(s) <= 500000 and 3 <= len(t) <= 500000, all bytes of s and t are lowercase ASCII letters (97..122), len(s) <= len(t), and s[i]=t[i] for every i with 0 <= i < len(s). -/
  theorem spec_11 (s t : Slice Std.U8)
      (hs_lo : 3 ≤ s.val.length) (hs_hi : s.val.length ≤ 500000)
      (ht_lo : 3 ≤ t.val.length) (ht_hi : t.val.length ≤ 500000)
      (hs_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (ht_lower : ∀ b ∈ t.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hlen : s.val.length ≤ t.val.length)
      (hagree : ∀ i : ℕ, i < s.val.length → s.val[i]? = t.val[i]?) :
      ∀ a b : Std.I64, maximum_length s = ok a → maximum_length t = ok b → a.val ≤ b.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_lo : 3 ≤ s.val.length) (hs_hi : s.val.length ≤ 500000)
        (ht_lo : 3 ≤ t.val.length) (ht_hi : t.val.length ≤ 500000)
        (hs_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (ht_lower : ∀ b ∈ t.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hlen : s.val.length ≤ t.val.length)
        (hagree : ∀ i : ℕ, i < s.val.length → s.val[i]? = t.val[i]?), ∀ a b : Std.I64, maximum_length s = ok a → maximum_length t = ok b → a.val ≤ b.val) := by
    sorry

  /-- Whenever maximum_length(s) returns a and maximum_length(t) returns b, we have a = b.
    Preconditions: Both s and t satisfy: 3 <= len(s) <= 500000 and 3 <= len(t) <= 500000, all bytes of s and t are lowercase ASCII letters (97..122), len(s)=len(t), and t[i]=s[len(s)-1-i] for every i with 0 <= i < len(s). -/
  theorem spec_12 (s t : Slice Std.U8)
      (hs_lo : 3 ≤ s.val.length) (hs_hi : s.val.length ≤ 500000)
      (ht_lo : 3 ≤ t.val.length) (ht_hi : t.val.length ≤ 500000)
      (hs_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (ht_lower : ∀ b ∈ t.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hlen : s.val.length = t.val.length)
      (hrev : ∀ i : ℕ, i < s.val.length → t.val[i]? = s.val[s.val.length - 1 - i]?) :
      ∀ a b : Std.I64, maximum_length s = ok a → maximum_length t = ok b → a.val = b.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_lo : 3 ≤ s.val.length) (hs_hi : s.val.length ≤ 500000)
        (ht_lo : 3 ≤ t.val.length) (ht_hi : t.val.length ≤ 500000)
        (hs_lower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (ht_lower : ∀ b ∈ t.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hlen : s.val.length = t.val.length)
        (hrev : ∀ i : ℕ, i < s.val.length → t.val[i]? = s.val[s.val.length - 1 - i]?), ∀ a b : Std.I64, maximum_length s = ok a → maximum_length t = ok b → a.val = b.val) := by
    sorry

  /-- Whenever maximum_length(s) returns a result r with r >= 1, for every integer L with 1 <= L <= r there exists a byte c such that Occ(c,L) >= 3, where Occ(c,L) is the number of indices i with 0 <= i <= len(s)-L and s[i+k]=c for all k with 0 <= k < L.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_13 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
        ∀ L : ℤ, 1 ≤ L → L ≤ r.val → ∃ c : Std.U8, 3 ≤ Occ s c L := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : Std.I64, maximum_length s = ok r → 1 ≤ r.val →
          ∀ L : ℤ, 1 ≤ L → L ≤ r.val → ∃ c : Std.U8, 3 ≤ Occ s c L) := by
    sorry

  /-- For every integer R with R >= 3, if there exist a and b with 0 <= a <= b < len(s), b-a+1=R, and s[k]=s[a] for every k with a <= k <= b, then whenever maximum_length(s) returns a result r, we have r >= R-2.
    Preconditions: 3 <= len(s) <= 500000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_14 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
      (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∀ R : ℤ, 3 ≤ R →
        (∃ a b : ℕ, a ≤ b ∧ b < s.val.length ∧ (b : ℤ) - (a : ℤ) + 1 = R ∧
          ∀ k : ℕ, a ≤ k → k ≤ b → s.val[k]? = s.val[a]?) →
        ∀ r : Std.I64, maximum_length s = ok r → R - 2 ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 500000)
        (hlower : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∀ R : ℤ, 3 ≤ R →
          (∃ a b : ℕ, a ≤ b ∧ b < s.val.length ∧ (b : ℤ) - (a : ℤ) + 1 = R ∧
            ∀ k : ℕ, a ≤ k → k ≤ b → s.val[k]? = s.val[a]?) →
          ∀ r : Std.I64, maximum_length s = ok r → R - 2 ≤ r.val) := by
    sorry

  end AegisSpec.MaximumLength
