import Aegis.NumDecodings.Code.Funs

/-!
# Specifications of `Aegis.NumDecodings.num_decodings`

LeetCode problem `decode-ways`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumDecodings (num_decodings)

  namespace AegisSpec.NumDecodings

  def lvals (l : List Std.U8) : List Nat := l.map (fun b => b.val)

  def dvals (s : Slice Std.U8) : List Nat := lvals s.val

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat := (s.val.getD i 0#u8).val

  def digitVal (s : Slice Std.U8) (i : Nat) : Int := (byteAt s i : Int) - 48

  def ok1 (c : Nat) : Bool := decide (49 ≤ c ∧ c ≤ 57)

  def ok2 (c d : Nat) : Bool :=
    decide (10 ≤ 10 * (c - 48) + (d - 48) ∧ 10 * (c - 48) + (d - 48) ≤ 26)

  abbrev Decoding := List (List Nat)

  def decodings : List Nat → List Decoding
    | [] => [[]]
    | [c] => if ok1 c then [[[c]]] else []
    | c :: d :: rest =>
      (if ok1 c then (decodings (d :: rest)).map (fun p => [c] :: p) else []) ++
        (if ok2 c d then (decodings rest).map (fun p => [c, d] :: p) else [])

  def D (l : List Nat) : Nat := (decodings l).length

  def fib : Nat → Nat
    | 0 => 0
    | 1 => 1
    | n + 2 => fib (n + 1) + fib n

  def ind (P : Prop) [Decidable P] : Int := if P then 1 else 0

  /-- Let n = len(s). A valid decoding of s is a partition of the index range {0,...,n-1} into consecutive blocks, each of size 1 or 2, such that (i) a size-1 block at index i is allowed exactly when s[i] is an ASCII digit from '1' to '9' (49 <= s[i] <= 57), and (ii) a size-2 block covering indices i and i+1 is allowed exactly when the two-digit number 10*(s[i]-48) + (s[i+1]-48) is between 10 and 26 inclusive. Let D(s) be the number of such partitions. For every s satisfying the preconditions, whenever num_decodings(s) returns a result r, r = D(s).
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); and the number of valid decodings of s, defined in the statement, is at most 2^31 - 1 (2147483647). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1) :
      ∀ r, num_decodings s = ok r → r.val = (D (dvals s) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1), ∀ r, num_decodings s = ok r → r.val = (D (dvals s) : Int)) := by
    sorry

  /-- For every s satisfying the preconditions, if for every contiguous substring t of s (including the empty substring) the number D(t) of valid decodings of t, defined as in spec_1 with D(empty)=1, is at most 2^63 - 1, then num_decodings(s) returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); and D(s) <= 2^31 - 1, where D(s) is the number of valid decodings of s as defined in spec_1. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (hsub : ∀ (i j : Nat), i ≤ j → j ≤ s.val.length →
        D (((dvals s).drop i).take (j - i)) ≤ 2 ^ 63 - 1) :
      ∃ r, num_decodings s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (hsub : ∀ (i j : Nat), i ≤ j → j ≤ s.val.length →
          D (((dvals s).drop i).take (j - i)) ≤ 2 ^ 63 - 1), ∃ r, num_decodings s = ok r) := by
    sorry

  /-- For every s satisfying the preconditions, whenever num_decodings(s) returns a result r, 0 <= r <= F(len(s)+1), where F(1)=1, F(2)=1, and F(k)=F(k-1)+F(k-2) for k > 2.
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); and D(s) <= 2^31 - 1, where D(s) is the number of valid decodings of s as defined in spec_1. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1) :
      ∀ r, num_decodings s = ok r → 0 ≤ r.val ∧ r.val ≤ (fib (s.val.length + 1) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1), ∀ r, num_decodings s = ok r → 0 ≤ r.val ∧ r.val ≤ (fib (s.val.length + 1) : Int)) := by
    sorry

  /-- If len(s) = 1, then whenever num_decodings(s) returns a result r, r = 1 if 49 <= s[0] <= 57, and r = 0 if s[0] = 48 ('0').
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); D(s) <= 2^31 - 1; and len(s) = 1. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (hlen1 : s.val.length = 1) :
      ∀ r, num_decodings s = ok r →
        ((49 ≤ byteAt s 0 ∧ byteAt s 0 ≤ 57) → r.val = 1) ∧ (byteAt s 0 = 48 → r.val = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (hlen1 : s.val.length = 1), ∀ r, num_decodings s = ok r →
          ((49 ≤ byteAt s 0 ∧ byteAt s 0 ≤ 57) → r.val = 1) ∧ (byteAt s 0 = 48 → r.val = 0)) := by
    sorry

  /-- If s[0] = 48 (the ASCII character '0'), then whenever num_decodings(s) returns a result r, r = 0.
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); D(s) <= 2^31 - 1; and s[0] = 48 ('0'). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (h0 : byteAt s 0 = 48) :
      ∀ r, num_decodings s = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (h0 : byteAt s 0 = 48), ∀ r, num_decodings s = ok r → r.val = 0) := by
    sorry

  /-- For every s satisfying the preconditions, whenever num_decodings(s) returns a result r, r > 0 if and only if for every index i with 0 <= i < len(s) and s[i] = 48 ('0'), we have i > 0 and (s[i-1] = 49 ('1') or s[i-1] = 50 ('2')).
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); and D(s) <= 2^31 - 1, where D(s) is the number of valid decodings of s as defined in spec_1. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1) :
      ∀ r, num_decodings s = ok r →
        (r.val > 0 ↔ ∀ i, i < s.val.length → byteAt s i = 48 →
          0 < i ∧ (byteAt s (i - 1) = 49 ∨ byteAt s (i - 1) = 50)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1), ∀ r, num_decodings s = ok r →
          (r.val > 0 ↔ ∀ i, i < s.val.length → byteAt s i = 48 →
            0 < i ∧ (byteAt s (i - 1) = 49 ∨ byteAt s (i - 1) = 50))) := by
    sorry

  /-- Under these preconditions, whenever num_decodings(s) returns a result r, r = F(len(s)+1), where F(1)=1, F(2)=1, and F(k)=F(k-1)+F(k-2) for k > 2.
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); D(s) <= 2^31 - 1; and for every i with 0 <= i < len(s), s[i] = 49 ('1') or s[i] = 50 ('2'). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (h12 : ∀ b ∈ s.val, b.val = 49 ∨ b.val = 50) :
      ∀ r, num_decodings s = ok r → r.val = (fib (s.val.length + 1) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (h12 : ∀ b ∈ s.val, b.val = 49 ∨ b.val = 50), ∀ r, num_decodings s = ok r → r.val = (fib (s.val.length + 1) : Int)) := by
    sorry

  /-- Under these preconditions, whenever num_decodings(s) returns a result r, r = 1.
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); D(s) <= 2^31 - 1; and for every i with 0 <= i < len(s), 51 <= s[i] <= 57 (the digit is one of '3','4','5','6','7','8','9'). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (h39 : ∀ b ∈ s.val, 51 ≤ b.val ∧ b.val ≤ 57) :
      ∀ r, num_decodings s = ok r → r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (h39 : ∀ b ∈ s.val, 51 ≤ b.val ∧ b.val ≤ 57), ∀ r, num_decodings s = ok r → r.val = 1) := by
    sorry

  /-- For every s satisfying the preconditions, if there exist byte slices p and q and a byte b such that b = 49 ('1') or b = 50 ('2'), and s is the concatenation p ++ [b, 48 ('0')] ++ q, then whenever num_decodings(s) returns a result r, r = D(p) * D(q), where D(t) is the number of valid decodings of a digit string t as defined in spec_1, with D(empty) = 1.
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); and D(s) <= 2^31 - 1, where D(s) is the number of valid decodings of s as defined in spec_1. -/
  theorem spec_9 (s : Slice Std.U8) (p q : List Std.U8) (b : Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ c ∈ s.val, 48 ≤ c.val ∧ c.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (hb : b.val = 49 ∨ b.val = 50)
      (hsplit : s.val = p ++ b :: 48#u8 :: q) :
      ∀ r, num_decodings s = ok r → r.val = (D (lvals p) * D (lvals q) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (p q : List Std.U8) (b : Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ c ∈ s.val, 48 ≤ c.val ∧ c.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (hb : b.val = 49 ∨ b.val = 50)
        (hsplit : s.val = p ++ b :: 48#u8 :: q), ∀ r, num_decodings s = ok r → r.val = (D (lvals p) * D (lvals q) : Int)) := by
    sorry

  /-- If s is the byte string '226', then num_decodings(s) returns a result r and r = 3.
    Preconditions: s is the byte string '226' (ASCII bytes [50, 50, 54]). -/
  theorem spec_10 (s : Slice Std.U8)
      (hs : s.val = [50#u8, 50#u8, 54#u8]) :
      ∃ r, num_decodings s = ok r ∧ r.val = 3 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hs : s.val = [50#u8, 50#u8, 54#u8]), ∃ r, num_decodings s = ok r ∧ r.val = 3) := by
    sorry

  /-- Let va = s[0] - 48 and vb = s[1] - 48. Whenever num_decodings(s) returns a result r, r = I(1 <= va <= 9 and 1 <= vb <= 9) + I(10 <= 10*va + vb <= 26), where I(true)=1 and I(false)=0.
    Preconditions: 1 <= len(s) <= 100; for every i with 0 <= i < len(s), s[i] is an ASCII digit (48 <= s[i] <= 57); D(s) <= 2^31 - 1; and len(s) = 2. -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
      (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hD : D (dvals s) ≤ 2 ^ 31 - 1)
      (hlen2 : s.val.length = 2) :
      ∀ r, num_decodings s = ok r →
        r.val = ind (1 ≤ digitVal s 0 ∧ digitVal s 0 ≤ 9 ∧ 1 ≤ digitVal s 1 ∧
              digitVal s 1 ≤ 9) +
            ind (10 ≤ 10 * digitVal s 0 + digitVal s 1 ∧
              10 * digitVal s 0 + digitVal s 1 ≤ 26) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlenle : s.val.length ≤ 100)
        (hdig : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hD : D (dvals s) ≤ 2 ^ 31 - 1)
        (hlen2 : s.val.length = 2), ∀ r, num_decodings s = ok r →
          r.val = ind (1 ≤ digitVal s 0 ∧ digitVal s 0 ≤ 9 ∧ 1 ≤ digitVal s 1 ∧
                digitVal s 1 ≤ 9) +
              ind (10 ≤ 10 * digitVal s 0 + digitVal s 1 ∧
                10 * digitVal s 0 + digitVal s 1 ≤ 26)) := by
    sorry

  end AegisSpec.NumDecodings
