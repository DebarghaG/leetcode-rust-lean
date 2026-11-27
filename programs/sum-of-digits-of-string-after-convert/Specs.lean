import Aegis.GetLucky.Code.Funs

/-!
# Specifications of `Aegis.GetLucky.get_lucky`

LeetCode problem `sum-of-digits-of-string-after-convert`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetLucky

open Aegis.GetLucky (get_lucky)

def digitSum (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => (m + 1) % 10 + digitSum ((m + 1) / 10)
termination_by n
decreasing_by
  show (m + 1) / 10 < m + 1
  omega

def digitSumIter : Nat → Nat → Nat
  | 0, n => n
  | j + 1, n => digitSumIter j (digitSum n)

def decDigits (n : Nat) : List Nat :=
  if n < 10 then [n] else decDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

def concatDigits (l : List Nat) : Nat :=
  l.foldl (fun acc d => acc * 10 + d) 0

def letterVal (b : Std.U8) : Nat := b.val - 96

def sliceDigitSum (s : Slice Std.U8) : Nat :=
  (s.val.map (fun b => digitSum (letterVal b))).sum

def sliceLetterSum (s : Slice Std.U8) : Nat := (s.val.map letterVal).sum

def concatVal (s : Slice Std.U8) : Nat :=
  concatDigits (s.val.flatMap (fun b => decDigits (letterVal b)))

/-- Let v(i) = s[i] - 96 for 0 <= i < len(s). Let D be the sequence of decimal digits obtained by writing v(0), v(1), ..., v(len(s)-1) in ordinary base 10 without leading zeros and concatenating these digit strings in that order. Let N be the integer represented by D. Let ds(n) be the sum of the decimal digits of n for n >= 0, and define ds^k by ds^0(n)=n and ds^(j+1)(n)=ds(ds^j(n)). For every valid input, get_lucky(s,k) returns a result r and r = ds^k(N).
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (lowercase ASCII); and 1 <= k <= 10. -/
theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10) :
    ∃ r : Std.I64,
      get_lucky s k = ok r ∧
        r.val = ((digitSumIter k.val.toNat (concatVal s) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10), ∃ r : Std.I64,
      get_lucky s k = ok r ∧
        r.val = ((digitSumIter k.val.toNat (concatVal s) : Nat) : Int)) := by
  sorry

/-- For every valid input, the call get_lucky(s,k) returns a result. No out-of-bounds access, panic, or 64-bit integer overflow occurs in forming the converted integer or in any of the k digit-sum steps.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and 1 <= k <= 10. -/
theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10) :
    ∃ r : Std.I64, get_lucky s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10), ∃ r : Std.I64, get_lucky s k = ok r) := by
  sorry

/-- For every valid input, whenever get_lucky(s,k) returns r, 1 <= r <= 10 * len(s).
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and 1 <= k <= 10. -/
theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10) :
    ∀ r : Std.I64,
      get_lucky s k = ok r → 1 ≤ r.val ∧ r.val ≤ 10 * (s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10), ∀ r : Std.I64,
      get_lucky s k = ok r → 1 ≤ r.val ∧ r.val ≤ 10 * (s.val.length : Int)) := by
  sorry

/-- Let S = sum_{i=0}^{len(s)-1} ds(s[i] - 96), where ds(v) is the sum of the decimal digits of v. For every valid input, whenever get_lucky(s,k) returns r, r = ds^(k-1)(S), with ds^0(S)=S.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and 1 <= k <= 10. -/
theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10) :
    ∀ r : Std.I64,
      get_lucky s k = ok r →
        r.val = ((digitSumIter (k.val.toNat - 1) (sliceDigitSum s) : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10), ∀ r : Std.I64,
      get_lucky s k = ok r →
        r.val = ((digitSumIter (k.val.toNat - 1) (sliceDigitSum s) : Nat) : Int)) := by
  sorry

/-- For every valid input with k >= 4, whenever get_lucky(s,k) returns r, r is the unique integer d such that 1 <= d <= 9 and N is congruent to d modulo 9, where N is the integer represented by the concatenation of the decimal representations of s[i] - 96 for i = 0, ..., len(s)-1, without leading zeros.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and 4 <= k <= 10. -/
theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 4 ≤ k.val) (hk_hi : k.val ≤ 10) :
    ∀ r : Std.I64,
      get_lucky s k = ok r →
        1 ≤ r.val ∧ r.val ≤ 9 ∧ Int.ModEq 9 ((concatVal s : Nat) : Int) r.val ∧
          ∀ d : Int, 1 ≤ d → d ≤ 9 → Int.ModEq 9 ((concatVal s : Nat) : Int) d → d = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 4 ≤ k.val) (hk_hi : k.val ≤ 10), ∀ r : Std.I64,
      get_lucky s k = ok r →
        1 ≤ r.val ∧ r.val ≤ 9 ∧ Int.ModEq 9 ((concatVal s : Nat) : Int) r.val ∧
          ∀ d : Int, 1 ≤ d → d ≤ 9 → Int.ModEq 9 ((concatVal s : Nat) : Int) d → d = r.val) := by
  sorry

/-- For every valid s and all such k1 and k2, the calls get_lucky(s,k1) and get_lucky(s,k2) return the same integer.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and k1, k2 satisfy 4 <= k1 <= 10 and 4 <= k2 <= 10. -/
theorem spec_6 (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk1_lo : 4 ≤ k1.val) (hk1_hi : k1.val ≤ 10)
    (hk2_lo : 4 ≤ k2.val) (hk2_hi : k2.val ≤ 10) :
    ∀ r1 r2 : Std.I64,
      get_lucky s k1 = ok r1 → get_lucky s k2 = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk1_lo : 4 ≤ k1.val) (hk1_hi : k1.val ≤ 10)
    (hk2_lo : 4 ≤ k2.val) (hk2_hi : k2.val ≤ 10), ∀ r1 r2 : Std.I64,
      get_lucky s k1 = ok r1 → get_lucky s k2 = ok r2 → r1.val = r2.val) := by
  sorry

/-- For every valid s and all such k1 and k2, if get_lucky(s,k1) returns r1 and get_lucky(s,k2) returns r2, then r2 <= r1.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and 1 <= k1 <= k2 <= 10. -/
theorem spec_7 (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 10) :
    ∀ r1 r2 : Std.I64,
      get_lucky s k1 = ok r1 → get_lucky s k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 10), ∀ r1 r2 : Std.I64,
      get_lucky s k1 = ok r1 → get_lucky s k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- For every valid input, whenever get_lucky(s,k) returns r, r is congruent modulo 9 to sum_{i=0}^{len(s)-1} (s[i] - 96).
  Preconditions: s is a byte slice with 1 <= len(s) <= 100; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; and 1 <= k <= 10. -/
theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10) :
    ∀ r : Std.I64,
      get_lucky s k = ok r → Int.ModEq 9 r.val ((sliceLetterSum s : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10), ∀ r : Std.I64,
      get_lucky s k = ok r → Int.ModEq 9 r.val ((sliceLetterSum s : Nat) : Int)) := by
  sorry

/-- For any two valid byte slices s and t and any valid k, if sum_{i=0}^{len(s)-1} ds(s[i] - 96) = sum_{j=0}^{len(t)-1} ds(t[j] - 96), where ds(v) is the decimal digit sum of v, then the calls get_lucky(s,k) and get_lucky(t,k) return the same integer.
  Preconditions: s and t are byte slices, each with length between 1 and 100; every byte of each is between 97 and 122; and 1 <= k <= 10. -/
theorem spec_9 (s t : Slice Std.U8) (k : Std.I64)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 100)
    (hs_bytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 100)
    (ht_bytes : ∀ (i : Nat) (hi : i < t.val.length),
      97 ≤ (t.val[i]).val ∧ (t.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10)
    (hsum : sliceDigitSum s = sliceDigitSum t) :
    ∀ r1 r2 : Std.I64,
      get_lucky s k = ok r1 → get_lucky t k = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 100)
    (hs_bytes : ∀ (i : Nat) (hi : i < s.val.length),
      97 ≤ (s.val[i]).val ∧ (s.val[i]).val ≤ 122)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 100)
    (ht_bytes : ∀ (i : Nat) (hi : i < t.val.length),
      97 ≤ (t.val[i]).val ∧ (t.val[i]).val ≤ 122)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10)
    (hsum : sliceDigitSum s = sliceDigitSum t), ∀ r1 r2 : Std.I64,
      get_lucky s k = ok r1 → get_lucky t k = ok r2 → r1.val = r2.val) := by
  sorry

end AegisSpec.GetLucky
