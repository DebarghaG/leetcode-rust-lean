import Aegis.QueryString.Code.Funs

/-!
# Specifications of `Aegis.QueryString.query_string`

LeetCode problem `binary-string-with-substrings-representing-1-to-n`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.QueryString

  def binDigits (k : ℕ) : ℕ → List ℕ
    | 0 => []
    | fuel + 1 => if k = 0 then [] else binDigits (k / 2) fuel ++ [k % 2]

  def bin (k : ℕ) : List U8 :=
    (binDigits k k).map (fun d => if d = 1 then 49#u8 else 48#u8)

  def IsSubstring (p : List U8) (s : Slice U8) : Prop :=
    ∃ j : ℕ, ∃ (_hj : j + p.length ≤ s.val.length),
      ∀ (t : ℕ) (ht : t < p.length), s.val[j + t]'(by omega) = p[t]

  def AllBins (s : Slice U8) (n : I64) : Prop :=
    ∀ k : ℕ, 1 ≤ k → k ≤ n.val.toNat → IsSubstring (bin k) s

  def firstByte (s : Slice U8) (h : 0 < s.length) : U8 :=
    s.val[0]'(by simp only [Aeneas.Std.Slice.length] at h ⊢; omega)

  /-- Let bin(k), for an integer k >= 1, be the unique nonempty byte sequence b of length L over {48 ('0'), 49 ('1')} such that b[0] = 49 and k = sum_{t=0}^{L-1} (b[t]-48) * 2^{L-1-t}; this is the usual binary representation with no leading zeros, encoded in ASCII. A byte sequence p is a contiguous substring of s if there exists an index j with 0 <= j and j + len(p) <= len(s) and p[t] = s[j+t] for every t with 0 <= t < len(p). Then query_string(s,n) returns Result.ok r (it does not fail) and r = true if and only if, for every integer k with 1 <= k <= n, bin(k) is a contiguous substring of s. If this condition fails, r = false.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_1 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9) :
      ∃ r : Bool, Aegis.QueryString.query_string s n = ok r ∧ (r = true ↔ AllBins s n) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9), ∃ r : Bool, Aegis.QueryString.query_string s n = ok r ∧ (r = true ↔ AllBins s n)) := by
    sorry

  /-- For every valid s and n, query_string(s,n) does not fail: it returns either Result.ok true or Result.ok false. No arithmetic overflow, index out of bounds, or panic occurs on these inputs.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_2 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9) :
      Aegis.QueryString.query_string s n = ok true ∨
        Aegis.QueryString.query_string s n = ok false := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9), Aegis.QueryString.query_string s n = ok true ∨
          Aegis.QueryString.query_string s n = ok false) := by
    sorry

  /-- If n >= 2^{len(s)} (the power computed as an integer), then query_string(s,n) returns Result.ok false.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_3 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
      (hbig : (2 : ℤ) ^ s.length ≤ n.val) :
      Aegis.QueryString.query_string s n = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
        (hbig : (2 : ℤ) ^ s.length ≤ n.val), Aegis.QueryString.query_string s n = ok false) := by
    sorry

  /-- Using bin(k) for the usual binary representation of k >= 1 as a byte sequence over {'0','1'} with no leading zero, if query_string(s,n) returns Result.ok true, then for every integer k with 1 <= k <= n, len(bin(k)) <= len(s). In particular, len(bin(n)) <= len(s).
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_4 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
      (hok : Aegis.QueryString.query_string s n = ok true) :
      (∀ k : ℕ, 1 ≤ k → k ≤ n.val.toNat → (bin k).length ≤ s.length) ∧
        (bin n.val.toNat).length ≤ s.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
        (hok : Aegis.QueryString.query_string s n = ok true), (∀ k : ℕ, 1 ≤ k → k ≤ n.val.toNat → (bin k).length ≤ s.length) ∧
          (bin n.val.toNat).length ≤ s.length) := by
    sorry

  /-- When n = 1, query_string(s,1) returns Result.ok true if and only if there exists an index j with 0 <= j < len(s) and s[j] = 49 (the byte '1'); otherwise it returns Result.ok false.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n = 1. -/
  theorem spec_5 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9) (hn_one : n.val = 1) :
      (Aegis.QueryString.query_string s n = ok true ↔
        ∃ j : ℕ, ∃ (_hj : j < s.length), (s.val[j]).val = 49) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9) (hn_one : n.val = 1), (Aegis.QueryString.query_string s n = ok true ↔
          ∃ j : ℕ, ∃ (_hj : j < s.length), (s.val[j]).val = 49)) := by
    sorry

  /-- If s contains only the byte 48 ('0'), then for every n with 1 <= n <= 10^9, query_string(s,n) returns Result.ok false.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and s[i] = 48 for every i with 0 <= i < len(s); n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_6 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hzero : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9) :
      Aegis.QueryString.query_string s n = ok false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hzero : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9), Aegis.QueryString.query_string s n = ok false) := by
    sorry

  /-- If len(s) = 1, then: (a) if s[0] = 49 and n = 1, query_string(s,n) returns Result.ok true; (b) if s[0] = 49 and n > 1, it returns Result.ok false; (c) if s[0] = 48, it returns Result.ok false for every n >= 1.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; len(s) = 1; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_7 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hlen_one : s.length = 1)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9) :
      (((firstByte s (by omega)).val = 49 ∧ n.val = 1) →
        Aegis.QueryString.query_string s n = ok true) ∧
      (((firstByte s (by omega)).val = 49 ∧ 1 < n.val) →
        Aegis.QueryString.query_string s n = ok false) ∧
      ((firstByte s (by omega)).val = 48 →
        Aegis.QueryString.query_string s n = ok false) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hlen_one : s.length = 1)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9), (((firstByte s (by omega)).val = 49 ∧ n.val = 1) →
          Aegis.QueryString.query_string s n = ok true) ∧
        (((firstByte s (by omega)).val = 49 ∧ 1 < n.val) →
          Aegis.QueryString.query_string s n = ok false) ∧
        ((firstByte s (by omega)).val = 48 →
          Aegis.QueryString.query_string s n = ok false)) := by
    sorry

  /-- If query_string(s,n1) returns Result.ok true, then query_string(s,n2) returns Result.ok true.
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n1 and n2 are integers with 1 <= n2 <= n1 <= 10^9. -/
  theorem spec_8 (s : Slice U8) (n1 n2 : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn2 : 1 ≤ n2.val) (hle : n2.val ≤ n1.val) (hn1_le : n1.val ≤ (10 : ℤ) ^ 9)
      (hok : Aegis.QueryString.query_string s n1 = ok true) :
      Aegis.QueryString.query_string s n2 = ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (n1 n2 : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn2 : 1 ≤ n2.val) (hle : n2.val ≤ n1.val) (hn1_le : n1.val ≤ (10 : ℤ) ^ 9)
        (hok : Aegis.QueryString.query_string s n1 = ok true), Aegis.QueryString.query_string s n2 = ok true) := by
    sorry

  /-- If query_string(s,n) returns Result.ok true, then query_string(t,n) returns Result.ok true.
    Preconditions: s and t are Slice of bytes with 1 <= len(s), len(t) <= 1000 and all their bytes are 48 or 49; s is a contiguous substring of t (there is j with 0 <= j and j+len(s) <= len(t) and s[i]=t[j+i] for all i < len(s)); n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_9 (s t : Slice U8) (n : I64)
      (hs : 1 ≤ s.length) (hs_le : s.length ≤ 1000)
      (ht : 1 ≤ t.length) (ht_le : t.length ≤ 1000)
      (hdigs : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hdigt : ∀ (i : ℕ) (hi : i < t.length), (t.val[i]).val = 48 ∨ (t.val[i]).val = 49)
      (hsub : IsSubstring s.val t)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
      (hok : Aegis.QueryString.query_string s n = ok true) :
      Aegis.QueryString.query_string t n = ok true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice U8) (n : I64)
        (hs : 1 ≤ s.length) (hs_le : s.length ≤ 1000)
        (ht : 1 ≤ t.length) (ht_le : t.length ≤ 1000)
        (hdigs : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hdigt : ∀ (i : ℕ) (hi : i < t.length), (t.val[i]).val = 48 ∨ (t.val[i]).val = 49)
        (hsub : IsSubstring s.val t)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
        (hok : Aegis.QueryString.query_string s n = ok true), Aegis.QueryString.query_string t n = ok true) := by
    sorry

  /-- Using bin(k) for the usual binary representation of k >= 1 as a byte sequence over {'0','1'} with no leading zero, for every integer k with 1 <= k <= n such that len(bin(k)) = len(s), if query_string(s,n) returns Result.ok true, then s = bin(k) byte-for-byte (i.e. len(s)=len(bin(k)) and s[i]=bin(k)[i] for all i < len(s)).
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_10 (s : Slice U8) (n : I64) (k : ℕ)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
      (hk_one : 1 ≤ k) (hk_n : k ≤ n.val.toNat) (hk_len : s.length = (bin k).length)
      (hok : Aegis.QueryString.query_string s n = ok true) :
      s.length = (bin k).length ∧
        ∀ (i : ℕ) (hi : i < s.length), s.val[i] = (bin k)[i]'(by omega) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (n : I64) (k : ℕ)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
        (hk_one : 1 ≤ k) (hk_n : k ≤ n.val.toNat) (hk_len : s.length = (bin k).length)
        (hok : Aegis.QueryString.query_string s n = ok true), s.length = (bin k).length ∧
          ∀ (i : ℕ) (hi : i < s.length), s.val[i] = (bin k)[i]'(by omega)) := by
    sorry

  /-- Using bin(k) for the usual binary representation of k >= 1 as a byte sequence over {'0','1'} with no leading zero, if query_string(s,n) returns Result.ok false, then there exists an integer k with 1 <= k <= n such that there is no index j satisfying 0 <= j, j+len(bin(k)) <= len(s), and s[j+t]=bin(k)[t] for all t with 0 <= t < len(bin(k)).
    Preconditions: s is a Slice of bytes with 1 <= len(s) <= 1000 and, for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49; n is an i64 with 1 <= n <= 10^9. -/
  theorem spec_11 (s : Slice U8) (n : I64)
      (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
      (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
      (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
      (hf : Aegis.QueryString.query_string s n = ok false) :
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n.val.toNat ∧ ¬ IsSubstring (bin k) s := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (n : I64)
        (hlen : 1 ≤ s.length) (hlen_le : s.length ≤ 1000)
        (hdig : ∀ (i : ℕ) (hi : i < s.length), (s.val[i]).val = 48 ∨ (s.val[i]).val = 49)
        (hn : 1 ≤ n.val) (hn_le : n.val ≤ (10 : ℤ) ^ 9)
        (hf : Aegis.QueryString.query_string s n = ok false), ∃ k : ℕ, 1 ≤ k ∧ k ≤ n.val.toNat ∧ ¬ IsSubstring (bin k) s) := by
    sorry

  end AegisSpec.QueryString
