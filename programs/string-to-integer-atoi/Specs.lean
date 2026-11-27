import Aegis.MyAtoi.Code.Funs

/-!
# Specifications of `Aegis.MyAtoi.my_atoi`

LeetCode problem `string-to-integer-atoi`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MyAtoi

abbrev Byte := Aeneas.Std.U8

abbrev ByteSlice := Aeneas.Std.Slice Aeneas.Std.U8

abbrev Int64 := Aeneas.Std.I64

theorem two_hundred_le_usize_max : (200 : Nat) ≤ Aeneas.Std.Usize.max := by
  simp [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num

def sval (s : ByteSlice) : List Byte := Aeneas.Std.Slice.val s

def bytes (s : ByteSlice) : List Nat := (sval s).map (fun b => b.val)

def isDigit (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

instance (c : Nat) : Decidable (isDigit c) := by unfold isDigit; infer_instance

def AllowedByte (c : Nat) : Prop :=
  isDigit c ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨
    c = 32 ∨ c = 43 ∨ c = 45 ∨ c = 46

def SlicePre (s : ByteSlice) : Prop :=
  (sval s).length ≤ 200 ∧ ∀ c ∈ bytes s, AllowedByte c

def skipSpaces : List Nat → Nat
  | [] => 0
  | c :: l => if c = 32 then 1 + skipSpaces l else 0

def digitPrefix : List Nat → Nat
  | [] => 0
  | c :: l => if isDigit c then 1 + digitPrefix l else 0

def digitsValue : List Nat → Nat
  | [] => 0
  | c :: l => (c - 48) * 10 ^ l.length + digitsValue l

structure ParseData where

  k : Nat

  sign : Int

  q : Nat

  m : Nat

  N : Nat

def parseData (l : List Nat) : ParseData :=
  let k := skipSpaces l
  let sign : Int := match l[k]? with
    | some 45 => -1
    | _ => 1
  let q := match l[k]? with
    | some 43 => k + 1
    | some 45 => k + 1
    | _ => k
  let N := digitsValue ((l.drop q).take (digitPrefix (l.drop q)))
  { k := k, sign := sign, q := q, m := q + digitPrefix (l.drop q), N := N }

def parse (s : ByteSlice) : ParseData := parseData (bytes s)

def val (s : ByteSlice) : Int :=
  let d := parse s
  if d.sign = 1 then min (d.N : Int) 2147483647 else max (-(d.N : Int)) (-2147483648)

theorem length_drop_le {α : Type} (l : List α) (n : Nat) : (l.drop n).length ≤ l.length := by
  rw [List.length_drop]
  exact Nat.sub_le _ _

def suffix (s : ByteSlice) (i : Nat) : ByteSlice :=
  Aeneas.Std.Slice.from ((sval s).drop i)
    (le_trans (length_drop_le _ _) (Aeneas.Std.Slice.length_ineq s))

def eraseAt (s : ByteSlice) (i : Nat) : ByteSlice :=
  Aeneas.Std.Slice.from ((sval s).eraseIdx i)
    (le_trans (List.length_eraseIdx_le _ _) (Aeneas.Std.Slice.length_ineq s))

def appendBytes (l₁ l₂ : List Byte) (h : (l₁ ++ l₂).length ≤ 200) : ByteSlice :=
  Aeneas.Std.Slice.from (l₁ ++ l₂) (le_trans h two_hundred_le_usize_max)

def lit (l : List Byte) (h : l.length ≤ 200) : ByteSlice :=
  Aeneas.Std.Slice.from l (le_trans h two_hundred_le_usize_max)

def input42 : ByteSlice := lit [52#u8, 50#u8] (by simp)

def inputSpaceNeg042 : ByteSlice := lit [32#u8, 45#u8, 48#u8, 52#u8, 50#u8] (by simp)

def input1337c0d3 : ByteSlice :=
  lit [49#u8, 51#u8, 51#u8, 55#u8, 99#u8, 48#u8, 100#u8, 51#u8] (by simp)

def input0minus1 : ByteSlice := lit [48#u8, 45#u8, 49#u8] (by simp)

def inputWordsAnd987 : ByteSlice :=
  lit [119#u8, 111#u8, 114#u8, 100#u8, 115#u8, 32#u8, 97#u8, 110#u8, 100#u8, 32#u8,
    57#u8, 56#u8, 55#u8] (by simp)

def inputMaxI32 : ByteSlice :=
  lit [50#u8, 49#u8, 52#u8, 55#u8, 52#u8, 56#u8, 51#u8, 54#u8, 52#u8, 55#u8] (by simp)

def inputMaxI32PlusOne : ByteSlice :=
  lit [50#u8, 49#u8, 52#u8, 55#u8, 52#u8, 56#u8, 51#u8, 54#u8, 52#u8, 56#u8] (by simp)

def inputMinI32 : ByteSlice :=
  lit [45#u8, 50#u8, 49#u8, 52#u8, 55#u8, 52#u8, 56#u8, 51#u8, 54#u8, 52#u8, 56#u8]
    (by simp)

def inputMinI32MinusOne : ByteSlice :=
  lit [45#u8, 50#u8, 49#u8, 52#u8, 55#u8, 52#u8, 56#u8, 51#u8, 54#u8, 52#u8, 57#u8]
    (by simp)

def inputHuge : ByteSlice :=
  lit [50#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8,
    48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8,
    48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8,
    48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8, 48#u8] (by simp)

theorem witness_inputs_satisfy_precondition :
    SlicePre input42 ∧ SlicePre inputSpaceNeg042 ∧ SlicePre input1337c0d3 ∧
    SlicePre input0minus1 ∧ SlicePre inputWordsAnd987 ∧ SlicePre inputMaxI32 ∧
    SlicePre inputMaxI32PlusOne ∧ SlicePre inputMinI32 ∧ SlicePre inputMinI32MinusOne ∧
    SlicePre inputHuge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [SlicePre, sval, bytes, AllowedByte, isDigit, input42, inputSpaceNeg042,
      input1337c0d3, input0minus1, inputWordsAnd987, inputMaxI32, inputMaxI32PlusOne,
      inputMinI32, inputMinI32MinusOne, inputHuge, lit]

/-- For every byte slice s satisfying the preconditions, the function returns a result r (it does not fail) and r = val(s), where val(s) is defined as follows. Let n = len(s). Let k be the smallest index in [0, n] such that k = n or s[k] != 32 (space); thus s[0..k) are all spaces. Let p = k. If p < n and (s[p] == 43 ('+') or s[p] == 45 ('-')), let sign = -1 if s[p] == 45 else +1, and let q = p + 1; otherwise let sign = +1 and q = p. Let m be the smallest index in [q, n] such that m = n or s[m] is not a digit (i.e., not (48 <= s[m] <= 57)). If m = q, set val(s) = 0. Otherwise let N = sum_{j=q}^{m-1} (s[j] - 48) * 10^(m-1-j) (a mathematical non-negative integer). Then if sign = +1, val(s) = min(N, 2147483647); if sign = -1, val(s) = max(-N, -2147483648).
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_1 (s : ByteSlice) (hpre : SlicePre s) :
    ∃ r : Int64, Aegis.MyAtoi.my_atoi s = ok r ∧ r.val = val s := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s), ∃ r : Int64, Aegis.MyAtoi.my_atoi s = ok r ∧ r.val = val s) := by
  sorry

/-- For every byte slice s satisfying the preconditions, the function returns a result r (i.e., it does not fail).
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_2 (s : ByteSlice) (hpre : SlicePre s) :
    ∃ r : Int64, Aegis.MyAtoi.my_atoi s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s), ∃ r : Int64, Aegis.MyAtoi.my_atoi s = ok r) := by
  sorry

/-- For every byte slice s satisfying the preconditions, whenever the function returns a result r, -2147483648 <= r <= 2147483647.
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_3 (s : ByteSlice) (hpre : SlicePre s) :
    ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r →
      (-2147483648 : Int) ≤ r.val ∧ r.val ≤ 2147483647 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s), ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r →
      (-2147483648 : Int) ≤ r.val ∧ r.val ≤ 2147483647) := by
  sorry

/-- For every byte slice s satisfying the preconditions, let n = len(s) and let k be the smallest index in [0, n] with k = n or s[k] != 32. If k = n, or if s[k] is not a digit and s[k] != 43 ('+') and s[k] != 45 ('-'), or if (s[k] == 43 or s[k] == 45) and (k+1 = n or s[k+1] is not a digit), then the function returns r = 0.
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_4 (s : ByteSlice) (hpre : SlicePre s)
    (hcase : (parse s).k = (bytes s).length ∨
      (∃ c, (bytes s)[(parse s).k]? = some c ∧ ¬ isDigit c ∧ c ≠ 43 ∧ c ≠ 45) ∨
      (∃ c, (bytes s)[(parse s).k]? = some c ∧ (c = 43 ∨ c = 45) ∧
        ∀ c', (bytes s)[(parse s).k + 1]? = some c' → ¬ isDigit c')) :
    ∃ r : Int64, Aegis.MyAtoi.my_atoi s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s)
    (hcase : (parse s).k = (bytes s).length ∨
      (∃ c, (bytes s)[(parse s).k]? = some c ∧ ¬ isDigit c ∧ c ≠ 43 ∧ c ≠ 45) ∨
      (∃ c, (bytes s)[(parse s).k]? = some c ∧ (c = 43 ∨ c = 45) ∧
        ∀ c', (bytes s)[(parse s).k + 1]? = some c' → ¬ isDigit c')), ∃ r : Int64, Aegis.MyAtoi.my_atoi s = ok r ∧ r.val = 0) := by
  sorry

/-- For every byte slice s satisfying the preconditions, let n = len(s) and let k be the smallest index in [0, n] with k = n or s[k] != 32. If k < n and s[k] == 45 ('-'), then the returned r satisfies r <= 0. If k < n and (s[k] == 43 ('+') or s[k] is a digit), then r >= 0. If k = n or s[k] is neither 43, 45, nor a digit, then r = 0.
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_5 (s : ByteSlice) (hpre : SlicePre s) :
    ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r →
      (((bytes s)[(parse s).k]? = some 45) → r.val ≤ 0) ∧
      (((bytes s)[(parse s).k]? = some 43 ∨
          ∃ c, (bytes s)[(parse s).k]? = some c ∧ isDigit c) → 0 ≤ r.val) ∧
      (((parse s).k = (bytes s).length ∨
          ∃ c, (bytes s)[(parse s).k]? = some c ∧ c ≠ 43 ∧ c ≠ 45 ∧ ¬ isDigit c) →
        r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s), ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r →
      (((bytes s)[(parse s).k]? = some 45) → r.val ≤ 0) ∧
      (((bytes s)[(parse s).k]? = some 43 ∨
          ∃ c, (bytes s)[(parse s).k]? = some c ∧ isDigit c) → 0 ≤ r.val) ∧
      (((parse s).k = (bytes s).length ∨
          ∃ c, (bytes s)[(parse s).k]? = some c ∧ c ≠ 43 ∧ c ≠ 45 ∧ ¬ isDigit c) →
        r.val = 0)) := by
  sorry

/-- For every byte slice s satisfying the preconditions, let n = len(s); let k be the smallest index in [0, n] with k = n or s[k] != 32; if k < n and (s[k] == 43 or s[k] == 45), let sign = -1 if s[k] == 45 else +1 and q = k+1, else sign = +1 and q = k; let m be the smallest index in [q, n] with m = n or s[m] not in [48, 57]; if m > q, let N = sum_{j=q}^{m-1} (s[j]-48)*10^(m-1-j); if m = q, let N = 0. If sign = -1 and N > 2147483648, then the returned r equals -2147483648.
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_6 (s : ByteSlice) (hpre : SlicePre s)
    (h : (parse s).sign = -1 ∧ 2147483648 < (parse s).N) :
    ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r → r.val = -2147483648 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s)
    (h : (parse s).sign = -1 ∧ 2147483648 < (parse s).N), ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r → r.val = -2147483648) := by
  sorry

/-- For every byte slice s satisfying the preconditions, with n, k, sign, q, m, N as defined in spec_6, if sign = +1 and N > 2147483647, then the returned r equals 2147483647.
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_7 (s : ByteSlice) (hpre : SlicePre s)
    (h : (parse s).sign = 1 ∧ 2147483647 < (parse s).N) :
    ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r → r.val = 2147483647 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s)
    (h : (parse s).sign = 1 ∧ 2147483647 < (parse s).N), ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r → r.val = 2147483647) := by
  sorry

/-- For every byte slice s satisfying the preconditions, with n, k, sign, q, m, N as defined in spec_6, if m > q and either (sign = +1 and N <= 2147483647) or (sign = -1 and N <= 2147483648), then the returned r equals N if sign = +1, and r equals -N if sign = -1.
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_8 (s : ByteSlice) (hpre : SlicePre s)
    (h : (parse s).q < (parse s).m ∧
      (((parse s).sign = 1 ∧ (parse s).N ≤ 2147483647) ∨
        ((parse s).sign = -1 ∧ (parse s).N ≤ 2147483648))) :
    ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r →
      (((parse s).sign = 1) → r.val = ((parse s).N : Int)) ∧
      (((parse s).sign = -1) → r.val = -((parse s).N : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s)
    (h : (parse s).q < (parse s).m ∧
      (((parse s).sign = 1 ∧ (parse s).N ≤ 2147483647) ∨
        ((parse s).sign = -1 ∧ (parse s).N ≤ 2147483648))), ∀ r : Int64, Aegis.MyAtoi.my_atoi s = ok r →
      (((parse s).sign = 1) → r.val = ((parse s).N : Int)) ∧
      (((parse s).sign = -1) → r.val = -((parse s).N : Int))) := by
  sorry

/-- For every byte slice s satisfying the preconditions, let n = len(s) and let k be the smallest index in [0, n] with k = n or s[k] != 32. Then the result of my_atoi(s) equals the result of my_atoi(s[k..n]) (the suffix obtained by removing all leading spaces).
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_9 (s : ByteSlice) (hpre : SlicePre s) :
    Aegis.MyAtoi.my_atoi s = Aegis.MyAtoi.my_atoi (suffix s (parse s).k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s), Aegis.MyAtoi.my_atoi s = Aegis.MyAtoi.my_atoi (suffix s (parse s).k)) := by
  sorry

/-- For every byte slice s satisfying the preconditions, let n = len(s); let k be the smallest index in [0, n] with k = n or s[k] != 32; if k < n and (s[k] == 43 or s[k] == 45), let q = k+1, else let q = k; let m be the smallest index in [q, n] with m = n or s[m] not in [48, 57]. If m < n, then for every byte slice u such that s ++ u satisfies the preconditions, the result of my_atoi(s ++ u) equals the result of my_atoi(s).
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_10 (s u : ByteSlice) (hpre : SlicePre s)
    (hlen : (sval s ++ sval u).length ≤ 200)
    (hall : ∀ c ∈ (sval s ++ sval u).map (fun b => b.val), AllowedByte c)
    (hm : (parse s).m < (bytes s).length) :
    Aegis.MyAtoi.my_atoi (appendBytes (sval s) (sval u) hlen) =
      Aegis.MyAtoi.my_atoi s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s u : ByteSlice) (hpre : SlicePre s)
    (hlen : (sval s ++ sval u).length ≤ 200)
    (hall : ∀ c ∈ (sval s ++ sval u).map (fun b => b.val), AllowedByte c)
    (hm : (parse s).m < (bytes s).length), Aegis.MyAtoi.my_atoi (appendBytes (sval s) (sval u) hlen) =
      Aegis.MyAtoi.my_atoi s) := by
  sorry

/-- For every byte slice s satisfying the preconditions, let n = len(s); let k be the smallest index in [0, n] with k = n or s[k] != 32; if k < n and (s[k] == 43 or s[k] == 45), let q = k+1, else let q = k; let m be the smallest index in [q, n] with m = n or s[m] not in [48, 57]. If m > q, s[q] == 48 ('0'), and (q > k or m > q + 1), then the result of my_atoi(s) equals the result of my_atoi(s with the byte at index q removed).
  Preconditions: 0 <= len(s) <= 200 and every byte of s is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_11 (s : ByteSlice) (hpre : SlicePre s)
    (hm : (parse s).q < (parse s).m)
    (hzero : (bytes s)[(parse s).q]? = some 48)
    (hcond : (parse s).k < (parse s).q ∨ (parse s).q + 1 < (parse s).m) :
    Aegis.MyAtoi.my_atoi s = Aegis.MyAtoi.my_atoi (eraseAt s (parse s).q) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : ByteSlice) (hpre : SlicePre s)
    (hm : (parse s).q < (parse s).m)
    (hzero : (bytes s)[(parse s).q]? = some 48)
    (hcond : (parse s).k < (parse s).q ∨ (parse s).q + 1 < (parse s).m), Aegis.MyAtoi.my_atoi s = Aegis.MyAtoi.my_atoi (eraseAt s (parse s).q)) := by
  sorry

/-- The function satisfies: my_atoi("42") = 42, my_atoi(" -042") = -42, my_atoi("1337c0d3") = 1337, my_atoi("0-1") = 0, my_atoi("words and 987") = 0.
  Preconditions: The listed input strings each satisfy 0 <= len(s) <= 200 and consist only of allowed characters. -/
theorem spec_12 :
    Aegis.MyAtoi.my_atoi input42 = ok 42#i64 ∧
    Aegis.MyAtoi.my_atoi inputSpaceNeg042 = ok (-42)#i64 ∧
    Aegis.MyAtoi.my_atoi input1337c0d3 = ok 1337#i64 ∧
    Aegis.MyAtoi.my_atoi input0minus1 = ok 0#i64 ∧
    Aegis.MyAtoi.my_atoi inputWordsAnd987 = ok 0#i64 := by
  sorry

theorem spec_12_neg :
    ¬ (Aegis.MyAtoi.my_atoi input42 = ok 42#i64 ∧
    Aegis.MyAtoi.my_atoi inputSpaceNeg042 = ok (-42)#i64 ∧
    Aegis.MyAtoi.my_atoi input1337c0d3 = ok 1337#i64 ∧
    Aegis.MyAtoi.my_atoi input0minus1 = ok 0#i64 ∧
    Aegis.MyAtoi.my_atoi inputWordsAnd987 = ok 0#i64) := by
  sorry

/-- The function satisfies: my_atoi("2147483647") = 2147483647, my_atoi("2147483648") = 2147483647, my_atoi("-2147483648") = -2147483648, my_atoi("-2147483649") = -2147483648, my_atoi("20000000000000000000000000000000000000000") = 2147483647.
  Preconditions: The listed input strings each satisfy 0 <= len(s) <= 200 and consist only of allowed characters. -/
theorem spec_13 :
    Aegis.MyAtoi.my_atoi inputMaxI32 = ok 2147483647#i64 ∧
    Aegis.MyAtoi.my_atoi inputMaxI32PlusOne = ok 2147483647#i64 ∧
    Aegis.MyAtoi.my_atoi inputMinI32 = ok (-2147483648)#i64 ∧
    Aegis.MyAtoi.my_atoi inputMinI32MinusOne = ok (-2147483648)#i64 ∧
    Aegis.MyAtoi.my_atoi inputHuge = ok 2147483647#i64 := by
  sorry

theorem spec_13_neg :
    ¬ (Aegis.MyAtoi.my_atoi inputMaxI32 = ok 2147483647#i64 ∧
    Aegis.MyAtoi.my_atoi inputMaxI32PlusOne = ok 2147483647#i64 ∧
    Aegis.MyAtoi.my_atoi inputMinI32 = ok (-2147483648)#i64 ∧
    Aegis.MyAtoi.my_atoi inputMinI32MinusOne = ok (-2147483648)#i64 ∧
    Aegis.MyAtoi.my_atoi inputHuge = ok 2147483647#i64) := by
  sorry

/-- For any two byte slices s and t satisfying the preconditions, let the parsing data for s be (k_s, sign_s, q_s, m_s, N_s) and for t be (k_t, sign_t, q_t, m_t, N_t), defined as follows: for a slice x, let n_x = len(x); let k_x be the smallest index in [0, n_x] with k_x = n_x or x[k_x] != 32; if k_x < n_x and (x[k_x] == 43 or x[k_x] == 45), let sign_x = -1 if x[k_x] == 45 else +1 and q_x = k_x+1, else sign_x = +1 and q_x = k_x; let m_x be the smallest index in [q_x, n_x] with m_x = n_x or x[m_x] not in [48, 57]; if m_x > q_x, let N_x = sum_{j=q_x}^{m_x-1} (x[j]-48)*10^(m_x-1-j); if m_x = q_x, let N_x = 0. If N_s = N_t and either N_s = 0 or sign_s = sign_t, then my_atoi(s) = my_atoi(t).
  Preconditions: Both s and t are byte slices with 0 <= len(s) <= 200, 0 <= len(t) <= 200, and every byte of s and t is one of: an English letter (a-z, A-Z), a digit '0'-'9', a space ' ', a plus '+', a minus '-', or a period '.'. -/
theorem spec_14 (s t : ByteSlice) (hpre_s : SlicePre s) (hpre_t : SlicePre t)
    (hN : (parse s).N = (parse t).N)
    (hsign : (parse s).N = 0 ∨ (parse s).sign = (parse t).sign) :
    Aegis.MyAtoi.my_atoi s = Aegis.MyAtoi.my_atoi t := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s t : ByteSlice) (hpre_s : SlicePre s) (hpre_t : SlicePre t)
    (hN : (parse s).N = (parse t).N)
    (hsign : (parse s).N = 0 ∨ (parse s).sign = (parse t).sign), Aegis.MyAtoi.my_atoi s = Aegis.MyAtoi.my_atoi t) := by
  sorry

end AegisSpec.MyAtoi
