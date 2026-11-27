import Aegis.FindGoodStrings.Code.Funs

/-!
# Specifications of `Aegis.FindGoodStrings.find_good_strings`

LeetCode problem `find-all-good-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindGoodStrings

  open Aegis.FindGoodStrings (find_good_strings)

  def lexLEB : List Std.U8 → List Std.U8 → Bool
    | [], _ => true
    | _ :: _, [] => false
    | a :: aas, b :: bs =>
        decide (a.val < b.val) || (decide (a.val = b.val) && lexLEB aas bs)

  @[reducible] def LexLE (s t : List Std.U8) : Prop := lexLEB s t = true

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def IsLowerBytes (l : List Std.U8) : Prop := ∀ b ∈ l, IsLowerByte b

  def OccursIn (evil w : List Std.U8) : Prop :=
    ∃ k : Nat, k + evil.length ≤ w.length ∧
      ∀ j : Nat, j < evil.length → w[k + j]? = evil[j]?

  def GoodString (n : Nat) (s1 s2 evil w : List Std.U8) : Prop :=
    w.length = n ∧ IsLowerBytes w ∧ LexLE s1 w ∧ LexLE w s2 ∧ ¬ OccursIn evil w

  def rangeSet (n : Nat) (s1 s2 : List Std.U8) : Set (List Std.U8) :=
    {w | w.length = n ∧ IsLowerBytes w ∧ LexLE s1 w ∧ LexLE w s2}

  noncomputable def countRange (n : Nat) (s1 s2 : List Std.U8) : Nat :=
    (rangeSet n s1 s2).ncard

  noncomputable def countGood (n : Nat) (s1 s2 evil : List Std.U8) : Nat :=
    {w | GoodString n s1 s2 evil w}.ncard

  noncomputable def countOverAlphabet (n : Nat) (p : List Std.U8 → Prop) : Nat :=
    {w | w.length = n ∧ IsLowerBytes w ∧ p w}.ncard

  def lexIndicator (s1 s2 w : List Std.U8) : Nat := if LexLE s1 w ∧ LexLE w s2 then 1 else 0

  def firstByte (l : List Std.U8) : Nat := (l.headD 0#u8).val

  def countSingletons (s1 s2 evil : List Std.U8) : Nat :=
    ((Finset.Icc 97 122).filter (fun c : Nat =>
        firstByte s1 ≤ c ∧ c ≤ firstByte s2 ∧
          (1 < evil.length ∨ c ≠ firstByte evil))).card

  /-- The function returns a result r, and r = C mod 1000000007, where C is the number of byte arrays w such that: len(w)=n; every byte of w is in [97,122]; s1 <=lex w and w <=lex s2, where <=lex is lexicographic order on equal-length byte arrays; and evil does not occur as a contiguous substring of w, meaning there is no k with 0 <= k and k+len(evil) <= n such that for every j with 0 <= j < len(evil), w[k+j]=evil[j]. Here mod means the canonical remainder in [0,1000000006].
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122] (lowercase ASCII); s1 <=lex s2, where <=lex is lexicographic order on equal-length byte arrays. -/
  theorem spec_1 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val) :
      ∃ r : Std.I64, find_good_strings n s1 s2 evil = ok r ∧
        r.val = ((countGood n.val.toNat s1.val s2.val evil.val % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val), ∃ r : Std.I64, find_good_strings n s1 s2 evil = ok r ∧
          r.val = ((countGood n.val.toNat s1.val s2.val evil.val % 1000000007 : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r of type Std.I64; it does not fail (no arithmetic overflow, out-of-bounds access, invalid slice access, or panic).
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_2 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val) :
      ∃ r : Std.I64, find_good_strings n s1 s2 evil = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val), ∃ r : Std.I64, find_good_strings n s1 s2 evil = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 1000000006.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_3 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r) :
      0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r), 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- Whenever the function returns a result r, if no byte array w of length n over lowercase ASCII satisfies s1 <=lex w <=lex s2 and contains evil as a contiguous substring, then r = I mod 1000000007, where I is the number of byte arrays w of length n over lowercase ASCII satisfying s1 <=lex w <=lex s2. In particular, this applies whenever len(evil) > n.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_4 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_no_evil : ¬ ∃ w : List Std.U8, w.length = n.val.toNat ∧ IsLowerBytes w ∧
        LexLE s1.val w ∧ LexLE w s2.val ∧ OccursIn evil.val w) :
      r.val = ((countRange n.val.toNat s1.val s2.val % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_no_evil : ¬ ∃ w : List Std.U8, w.length = n.val.toNat ∧ IsLowerBytes w ∧
          LexLE s1.val w ∧ LexLE w s2.val ∧ OccursIn evil.val w), r.val = ((countRange n.val.toNat s1.val s2.val % 1000000007 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if s1 = s2 as byte arrays, then r = 1 if s1 does not contain evil as a contiguous substring, and r = 0 if s1 does contain evil as a contiguous substring.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]. -/
  theorem spec_5 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_eq : s1.val = s2.val) :
      (OccursIn evil.val s1.val → r.val = 0) ∧ (¬ OccursIn evil.val s1.val → r.val = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_eq : s1.val = s2.val), (OccursIn evil.val s1.val → r.val = 0) ∧ (¬ OccursIn evil.val s1.val → r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, if len(evil) = n, then r = (I - B) mod 1000000007, where I is the number of length-n lowercase ASCII byte arrays w with s1 <=lex w <=lex s2, and B is 1 if s1 <=lex evil <=lex s2 and 0 otherwise.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_6 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_evil_n : evil.val.length = n.val.toNat) :
      r.val = (((countRange n.val.toNat s1.val s2.val -
        lexIndicator s1.val s2.val evil.val) % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_evil_n : evil.val.length = n.val.toNat), r.val = (((countRange n.val.toNat s1.val s2.val -
          lexIndicator s1.val s2.val evil.val) % 1000000007 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if s1 is the length-n byte array consisting entirely of byte 97 ('a') and s2 is the length-n byte array consisting entirely of byte 122 ('z'), then r = (26^n - B) mod 1000000007, where B is the number of length-n byte arrays over lowercase ASCII that contain evil as a contiguous substring.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]. -/
  theorem spec_7 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_s1 : s1.val = List.replicate n.val.toNat 97#u8)
      (h_s2 : s2.val = List.replicate n.val.toNat 122#u8) :
      r.val = ((((26 ^ n.val.toNat) -
        countOverAlphabet n.val.toNat (fun w => OccursIn evil.val w)) %
          1000000007 : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_s1 : s1.val = List.replicate n.val.toNat 97#u8)
        (h_s2 : s2.val = List.replicate n.val.toNat 122#u8), r.val = ((((26 ^ n.val.toNat) -
          countOverAlphabet n.val.toNat (fun w => OccursIn evil.val w)) %
            1000000007 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if r != 0, then there exists at least one good string: a byte array w with len(w)=n, all bytes in [97,122], s1 <=lex w <=lex s2, and evil not occurring as a contiguous substring of w.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_8 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_ne : r.val ≠ 0) :
      ∃ w : List Std.U8, GoodString n.val.toNat s1.val s2.val evil.val w := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_ne : r.val ≠ 0), ∃ w : List Std.U8, GoodString n.val.toNat s1.val s2.val evil.val w) := by
    sorry

  /-- Whenever the function returns a result r, if the exact number C of good strings, where C is the number of length-n lowercase ASCII byte arrays w with s1 <=lex w <=lex s2 and with evil not occurring as a contiguous substring of w, is less than 1000000007, then r = C.
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_9 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_C : countGood n.val.toNat s1.val s2.val evil.val < 1000000007) :
      r.val = ((countGood n.val.toNat s1.val s2.val evil.val : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_C : countGood n.val.toNat s1.val s2.val evil.val < 1000000007), r.val = ((countGood n.val.toNat s1.val s2.val evil.val : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if n = 1, then r = A mod 1000000007, where A is the number of integers c with 97 <= c <= 122, s1[0] <= c <= s2[0], and (len(evil) > 1 or c != evil[0]).
    Preconditions: n is an integer with 1 <= n <= 500; interpreting n as a natural number, len(s1) = len(s2) = n; 1 <= len(evil) <= 50; every byte of s1, s2, and evil is in [97,122]; s1 <=lex s2. -/
  theorem spec_10 (n : Std.I64) (s1 s2 evil : Slice Std.U8)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
      (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
      (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
      (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
      (h_lowE : IsLowerBytes evil.val)
      (h_lex : LexLE s1.val s2.val)
      (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
      (h_n : n.val = 1) :
      r.val = ((countSingletons s1.val s2.val evil.val % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (s1 s2 evil : Slice Std.U8)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 500)
        (h_len1 : s1.val.length = n.val.toNat) (h_len2 : s2.val.length = n.val.toNat)
        (h_evil_lo : 1 ≤ evil.val.length) (h_evil_hi : evil.val.length ≤ 50)
        (h_low1 : IsLowerBytes s1.val) (h_low2 : IsLowerBytes s2.val)
        (h_lowE : IsLowerBytes evil.val)
        (h_lex : LexLE s1.val s2.val)
        (r : Std.I64) (hr : find_good_strings n s1 s2 evil = ok r)
        (h_n : n.val = 1), r.val = ((countSingletons s1.val s2.val evil.val % 1000000007 : Nat) : Int)) := by
    sorry

  end AegisSpec.FindGoodStrings
