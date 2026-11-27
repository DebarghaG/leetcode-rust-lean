import Aegis.FindSubstringInWraproundString.Code.Funs

/-!
# Specifications of `Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string`

LeetCode problem `unique-substrings-in-wraparound-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindSubstringInWraproundString

  def byteVal (c : Aeneas.Std.U8) : Nat := c.val

  def vals (s : Aeneas.Std.Slice Aeneas.Std.U8) : List Nat := s.val.map byteVal

  def at? (l : List Aeneas.Std.U8) (i : Nat) : Option Nat := (l[i]?).map byteVal

  def seg (s : Aeneas.Std.Slice Aeneas.Std.U8) (i j : Nat) : List Nat :=
    ((s.val.drop i).take (j - i)).map byteVal

  def succVal (c : Nat) : Nat := if c = 122 then 97 else c + 1

  def IsCyclicSucc (a b : Nat) : Prop := b = succVal a

  def BaseValidB : List Nat → Bool
    | [] => true
    | [_] => true
    | a :: b :: rest => (b == succVal a) && BaseValidB (b :: rest)

  def BaseValid (l : List Nat) : Prop := BaseValidB l = true

  instance instDecidablePredBaseValid : DecidablePred BaseValid := fun l =>
    decidable_of_iff (BaseValidB l = true) (Iff.rfl : BaseValidB l = true ↔ BaseValid l)

  def indexPairs (s : Aeneas.Std.Slice Aeneas.Std.U8) : Finset (Nat × Nat) :=
    Finset.filter (fun p : Nat × Nat => p.1 < p.2)
      ((Finset.range (s.val.length + 1)).product (Finset.range (s.val.length + 1)))

  def validSpans (s : Aeneas.Std.Slice Aeneas.Std.U8) : Finset (Nat × Nat) :=
    Finset.filter
      (fun p : Nat × Nat =>
        1 ≤ p.2 ∧ p.1 + p.2 ≤ s.val.length ∧ BaseValid (seg s p.1 (p.1 + p.2)))
      ((Finset.range (s.val.length + 1)).product (Finset.range (s.val.length + 1)))

  def U (s : Aeneas.Std.Slice Aeneas.Std.U8) : Finset (List Nat) :=
    Finset.filter BaseValid
      ((indexPairs s).image (fun p : Nat × Nat => seg s p.1 p.2))

  def firstBytes (s : Aeneas.Std.Slice Aeneas.Std.U8) : Finset Nat :=
    (U s).image (fun t => t.headD 0)

  def firstByteCount (s : Aeneas.Std.Slice Aeneas.Std.U8) (c : Nat) : Nat :=
    ((U s).filter (fun t => t.headD 0 = c)).card

  def letters (s : Aeneas.Std.Slice Aeneas.Std.U8) : Finset Nat :=
    Finset.filter (fun c : Nat => c ∈ vals s) (Finset.Icc 97 122)

  def letterCount (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat := (letters s).card

  def firstPos (s : Aeneas.Std.Slice Aeneas.Std.U8) (c : Nat) : Nat := (vals s).idxOf c

  def Lmax (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat :=
    (validSpans s).sup (fun p : Nat × Nat => p.2)

  def maxLenWithFirst (s : Aeneas.Std.Slice Aeneas.Std.U8) (c : Nat) : Nat :=
    ((validSpans s).filter (fun p : Nat × Nat => at? s.val p.1 = some c)).sup
      (fun p : Nat × Nat => p.2)

  def countValidSubstrings (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat :=
    ((indexPairs s).filter (fun p : Nat × Nat => BaseValid (seg s p.1 p.2))).card

  def cycRun : Nat → Nat → List Nat
    | _, 0 => []
    | c, (L + 1) => c :: cycRun (succVal c) L

  /-- Let U(s) be the set of all non-empty byte sequences t such that (1) t is base-valid: for every k with 0 <= k < len(t)-1, t[k+1] is the cyclic successor of t[k], meaning t[k+1] = 97 if t[k] = 122, and t[k+1] = t[k] + 1 otherwise; and (2) t occurs as a contiguous substring of s: there exist i and j with 0 <= i < j <= n, len(t) = j - i, and t[k] = s[i+k] for every 0 <= k < j - i. The function returns an I64 result r and r = |U(s)|, the number of distinct non-empty substrings of s that are present in the infinite wraparound string base. Distinctness is equality of byte sequences, so repeated occurrences of the same bytes are counted once.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val = ((U s).card : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val = ((U s).card : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns some I64 value r; it does not fail (no panic, no out-of-bounds access, and no integer overflow).
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r) := by
    sorry

  /-- The function returns a result r with 1 <= r <= 26 * n.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        1 ≤ r.val ∧ r.val ≤ ((26 * n : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          1 ≤ r.val ∧ r.val ≤ ((26 * n : Nat) : Int)) := by
    sorry

  /-- The function returns a result r with r <= n * (n + 1) / 2.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val ≤ ((n * (n + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val ≤ ((n * (n + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- The function returns a result r with r >= d, where d is the number of distinct byte values c in the range 97 <= c <= 122 that occur in s, i.e. for which there exists i with 0 <= i < n and s[i] = c.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        ((letterCount s : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          ((letterCount s : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Let Lmax be the maximum length L such that 1 <= L <= n and there exists an index i with 0 <= i, i + L <= n, and the substring s[i..i+L] is base-valid, where base-valid means every adjacent pair advances by one letter cyclically from a to z and from z to a. The function returns a result r with r >= Lmax.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        ((Lmax s : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          ((Lmax s : Nat) : Int) ≤ r.val) := by
    sorry

  /-- For each byte c with 97 <= c <= 122, let M(c) be 0 if c does not occur in s; otherwise let M(c) be the maximum L >= 1 such that for some index i, 0 <= i, i + L <= n, s[i] = c, and s[i..i+L] is base-valid. Let N(c) be the number of distinct counted substrings (the elements of U(s) from the main specification) whose first byte is c. Then for every c, N(c) = M(c), and the function returns r = sum over c from 97 to 122 of M(c).
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        (∀ c, 97 ≤ c → c ≤ 122 → firstByteCount s c = maxLenWithFirst s c) ∧
        r.val = (((Finset.Icc 97 122).sum (fun c => maxLenWithFirst s c) : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          (∀ c, 97 ≤ c → c ≤ 122 → firstByteCount s c = maxLenWithFirst s c) ∧
          r.val = (((Finset.Icc 97 122).sum (fun c => maxLenWithFirst s c) : Nat) : Int)) := by
    sorry

  /-- The function returns a result r with r = d, where d is the number of distinct byte values occurring in s.
    Preconditions: n = len(s); 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= s[i] <= 122; and for every i with 0 <= i < n-1, s[i+1] is not the cyclic successor of s[i]. -/
  theorem spec_8 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122)
      (hstep : ∀ i a b, i + 1 < n → at? s.val i = some a → at? s.val (i + 1) = some b →
        ¬ IsCyclicSucc a b) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val = ((letterCount s : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122)
        (hstep : ∀ i a b, i + 1 < n → at? s.val i = some a → at? s.val (i + 1) = some b →
          ¬ IsCyclicSucc a b), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val = ((letterCount s : Nat) : Int)) := by
    sorry

  /-- For each byte c with 97 <= c <= 122 that occurs in s, let firstpos(c) be the minimum i such that 0 <= i < n and s[i] = c. The function returns a result r with r = sum over such c of (n - firstpos(c)).
    Preconditions: n = len(s); 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= s[i] <= 122; and for every i with 0 <= i < n-1, s[i+1] is the cyclic successor of s[i]. -/
  theorem spec_9 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122)
      (hstep : ∀ i a b, i + 1 < n → at? s.val i = some a → at? s.val (i + 1) = some b →
        IsCyclicSucc a b) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val = (((letters s).sum (fun c => n - firstPos s c) : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122)
        (hstep : ∀ i a b, i + 1 < n → at? s.val i = some a → at? s.val (i + 1) = some b →
          IsCyclicSucc a b), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val = (((letters s).sum (fun c => n - firstPos s c) : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r equals the number of pairs (i,j) with 0 <= i < j <= n such that s[i..j] is base-valid.
    Preconditions: n = len(s); 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= s[i] <= 122; and the bytes s[0],...,s[n-1] are pairwise distinct. -/
  theorem spec_10 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122)
      (hdistinct : (vals s).Nodup) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val = ((countValidSubstrings s : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122)
        (hdistinct : (vals s).Nodup), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val = ((countValidSubstrings s : Nat) : Int)) := by
    sorry

  /-- For each byte c with 97 <= c <= 122, let M(c) be 0 if c does not occur in s; otherwise let M(c) be the maximum L >= 1 such that for some index i, 0 <= i, i + L <= n, s[i] = c, and s[i..i+L] is base-valid. Then for every integer L with 1 <= L <= M(c), there exists an index i with 0 <= i, i + L <= n, s[i] = c, and s[i..i+L] base-valid; consequently the length-L byte sequence starting with c and following cyclic successors is one of the distinct substrings counted in r.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_11 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        ∀ c, 97 ≤ c → c ≤ 122 → ∀ L, 1 ≤ L → L ≤ maxLenWithFirst s c →
          (∃ i, i + L ≤ n ∧ at? s.val i = some c ∧ BaseValid (seg s i (i + L))) ∧
          cycRun c L ∈ U s := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          ∀ c, 97 ≤ c → c ≤ 122 → ∀ L, 1 ≤ L → L ≤ maxLenWithFirst s c →
            (∃ i, i + L ≤ n ∧ at? s.val i = some c ∧ BaseValid (seg s i (i + L))) ∧
            cycRun c L ∈ U s) := by
    sorry

  /-- The function returns a result r, and the set of first bytes of the r distinct counted substrings is exactly the set of byte values c with 97 <= c <= 122 that occur in s.
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_12 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val = ((U s).card : Int) ∧ firstBytes s = letters s := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val = ((U s).card : Int) ∧ firstBytes s = letters s) := by
    sorry

  /-- The function returns a result r, and the set U(s) of the r distinct counted substrings is closed under taking non-empty contiguous substrings: if t belongs to U(s) and 0 <= a < b <= len(t), then the byte sequence t[a..b] also belongs to U(s).
    Preconditions: n = len(s); 1 <= n <= 100000; and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_13 (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hbound : n ≤ 100000)
      (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
        r.val = ((U s).card : Int) ∧
        ∀ t ∈ U s, ∀ a b, a < b → b ≤ t.length → (t.drop a).take (b - a) ∈ U s := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hbound : n ≤ 100000)
        (hbytes : ∀ c ∈ vals s, 97 ≤ c ∧ c ≤ 122), ∃ r : Aeneas.Std.I64,
          Aegis.FindSubstringInWraproundString.find_substring_in_wrapround_string s = ok r ∧
          r.val = ((U s).card : Int) ∧
          ∀ t ∈ U s, ∀ a b, a < b → b ≤ t.length → (t.drop a).take (b - a) ∈ U s) := by
    sorry

  end AegisSpec.FindSubstringInWraproundString
