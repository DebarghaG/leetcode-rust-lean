import Aegis.ConfusingNumberIi.Code.Funs

/-!
# Specifications of `Aegis.ConfusingNumberIi.confusing_number_ii`

LeetCode problem `confusing-number-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ConfusingNumberIi

  def revDigitsAux : Nat → Nat → List Nat
    | 0, _ => []
    | k + 1, x => if x = 0 then [] else x % 10 :: revDigitsAux k (x / 10)

  def revDigits (x : Nat) : List Nat := revDigitsAux (x + 1) x

  def digits (x : Nat) : List Nat := (revDigits x).reverse

  def ValidDigit (d : Nat) : Prop := d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 8 ∨ d = 9

  def validDigitB (d : Nat) : Bool := d == 0 || d == 1 || d == 6 || d == 8 || d == 9

  def ForbiddenDigit (d : Nat) : Prop := d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 7

  def HasOnlyValidDigits (x : Nat) : Prop := ∀ d ∈ digits x, ValidDigit d

  def HasForbiddenDigit (x : Nat) : Prop := ∃ d ∈ digits x, ForbiddenDigit d

  def hasOnlyValidDigitsB (x : Nat) : Bool := (digits x).all validDigitB

  def rotDigit (d : Nat) : Nat :=
    if d = 1 then 1 else if d = 6 then 9 else if d = 8 then 8 else if d = 9 then 6 else 0

  def ofDigits (l : List Nat) : Nat := l.foldl (fun acc d => acc * 10 + d) 0

  def flip (x : Nat) : Nat := ofDigits ((digits x).map rotDigit).reverse

  def Confusing (x : Nat) : Prop := 1 ≤ x ∧ HasOnlyValidDigits x ∧ flip x ≠ x

  def confusingB (x : Nat) : Bool := decide (1 ≤ x) && hasOnlyValidDigitsB x && (flip x != x)

  def countUpTo (n : Nat) (p : Nat → Bool) : Nat := ((List.range (n + 1)).filter p).length

  def V (n : Nat) : Nat :=
    countUpTo n (fun x => decide (1 ≤ x) && hasOnlyValidDigitsB x)

  def F (n : Nat) : Nat :=
    countUpTo n (fun x => decide (1 ≤ x) && hasOnlyValidDigitsB x && (flip x == x))

  def confusingCount (n : Nat) : Nat := countUpTo n confusingB

  def i64OfNat (x : Nat) : Std.I64 := ⟨BitVec.ofNat 64 x⟩

  /-- Let rot be the map rot(0)=0, rot(1)=1, rot(6)=9, rot(8)=8, and rot(9)=6. Call a positive integer x confusing when every decimal digit of x belongs to {0,1,6,8,9}, and, writing d_1...d_k for the decimal representation of x with d_1 != 0, the integer obtained from rot(d_k) rot(d_{k-1}) ... rot(d_1) after deleting all leading zeros and interpreting an all-zero or empty string as 0 is different from x. For every n with 1 <= n <= 1000000000, confusing_number_ii(n) returns a result r and r = |{x in integers : 1 <= x <= n and x is confusing}|.
    Preconditions: n is an integer with 1 <= n <= 1000000000. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r ∧
          r.val = (confusingCount n.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r ∧
            r.val = (confusingCount n.val.toNat : Int)) := by
    sorry

  /-- confusing_number_ii(n) returns a result; it does not fail, panic, or overflow.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.ConfusingNumberIi.confusing_number_ii n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∃ r : Std.I64, Aegis.ConfusingNumberIi.confusing_number_ii n = ok r) := by
    sorry

  /-- Whenever confusing_number_ii(n) returns r, 0 <= r <= n.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
          0 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
            0 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- confusing_number_ii(n) returns r and r = (if n >= 6 then 1 else 0) + (if n >= 9 then 1 else 0).
    Preconditions: 1 <= n <= 9. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 9) :
      ∃ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r ∧
          r.val = (if 6 ≤ n.val then (1 : Int) else 0) +
                  (if 9 ≤ n.val then (1 : Int) else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 9), ∃ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r ∧
            r.val = (if 6 ≤ n.val then (1 : Int) else 0) +
                    (if 9 ≤ n.val then (1 : Int) else 0)) := by
    sorry

  /-- Let V(n) be the number of integers x with 1 <= x <= n such that every decimal digit of x belongs to {0,1,6,8,9}. Whenever confusing_number_ii(n) returns r, r <= V(n).
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
          r.val ≤ (V n.val.toNat : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
            r.val ≤ (V n.val.toNat : Int)) := by
    sorry

  /-- Whenever confusing_number_ii(n) returns r, r >= 19.
    Preconditions: 100 <= n <= 1000000000. -/
  theorem spec_6 (n : Std.I64) (hn : 100 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r → 19 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : 100 ≤ n.val) (hn' : n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r → 19 ≤ r.val) := by
    sorry

  /-- Whenever confusing_number_ii(n) returns r_n and confusing_number_ii(m) returns r_m, r_n <= r_m.
    Preconditions: 1 <= n <= m <= 1000000000. -/
  theorem spec_7 (n m : Std.I64) (hn : 1 ≤ n.val) (hnm : n.val ≤ m.val)
      (hm : m.val ≤ 1000000000) :
      ∀ rn rm : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok rn →
          Aegis.ConfusingNumberIi.confusing_number_ii m = ok rm → rn.val ≤ rm.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m : Std.I64) (hn : 1 ≤ n.val) (hnm : n.val ≤ m.val)
        (hm : m.val ≤ 1000000000), ∀ rn rm : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok rn →
            Aegis.ConfusingNumberIi.confusing_number_ii m = ok rm → rn.val ≤ rm.val) := by
    sorry

  /-- Whenever confusing_number_ii(n) returns r and confusing_number_ii(n+1) returns s, s - r is 1 if n+1 is confusing and 0 otherwise, where n+1 is confusing if every decimal digit of n+1 belongs to {0,1,6,8,9} and its 180-degree rotation, after deleting leading zeros, is not equal to n+1.
    Preconditions: 1 <= n < 1000000000. -/
  theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val < 1000000000) :
      ∀ r s : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
          Aegis.ConfusingNumberIi.confusing_number_ii (i64OfNat (n.val.toNat + 1)) = ok s →
            s.val - r.val = (if confusingB (n.val.toNat + 1) then (1 : Int) else 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val < 1000000000), ∀ r s : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
            Aegis.ConfusingNumberIi.confusing_number_ii (i64OfNat (n.val.toNat + 1)) = ok s →
              s.val - r.val = (if confusingB (n.val.toNat + 1) then (1 : Int) else 0)) := by
    sorry

  /-- Whenever confusing_number_ii(n-1) returns a and confusing_number_ii(n) returns b, a = b.
    Preconditions: 2 <= n <= 1000000000 and the decimal representation of n contains at least one of the digits 2,3,4,5,7. -/
  theorem spec_9 (n : Std.I64) (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000000000)
      (hbad : HasForbiddenDigit n.val.toNat) :
      ∀ a b : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii (i64OfNat (n.val.toNat - 1)) = ok a →
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok b → a.val = b.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : 2 ≤ n.val) (hn' : n.val ≤ 1000000000)
        (hbad : HasForbiddenDigit n.val.toNat), ∀ a b : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii (i64OfNat (n.val.toNat - 1)) = ok a →
            Aegis.ConfusingNumberIi.confusing_number_ii n = ok b → a.val = b.val) := by
    sorry

  /-- Whenever confusing_number_ii(n) returns r and r > 0, there exists an integer x with 1 <= x <= n such that every decimal digit of x belongs to {0,1,6,8,9} and the 180-degree rotation of x, after deleting leading zeros, is not equal to x.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_10 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r → 0 < r.val →
          ∃ x : Nat, 1 ≤ x ∧ x ≤ n.val.toNat ∧ HasOnlyValidDigits x ∧ flip x ≠ x := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r → 0 < r.val →
            ∃ x : Nat, 1 ≤ x ∧ x ≤ n.val.toNat ∧ HasOnlyValidDigits x ∧ flip x ≠ x) := by
    sorry

  /-- Whenever confusing_number_ii(n) returns r and r = 0, for every integer x with 1 <= x <= n, either x has a decimal digit in {2,3,4,5,7} or the 180-degree rotation of x, after deleting leading zeros, equals x.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_11 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r → r.val = 0 →
          ∀ x : Nat, 1 ≤ x → x ≤ n.val.toNat → HasForbiddenDigit x ∨ flip x = x := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r → r.val = 0 →
            ∀ x : Nat, 1 ≤ x → x ≤ n.val.toNat → HasForbiddenDigit x ∨ flip x = x) := by
    sorry

  /-- Let rot be the map rot(0)=0, rot(1)=1, rot(6)=9, rot(8)=8, rot(9)=6. For x with decimal representation d_1...d_k (d_1 != 0) and all digits in {0,1,6,8,9}, let flip(x) be the integer obtained from rot(d_k)...rot(d_1) after deleting leading zeros, interpreting an empty or all-zero string as 0. Define V(n) = |{x : 1 <= x <= n and every decimal digit of x belongs to {0,1,6,8,9}}| and F(n) = |{x : 1 <= x <= n, every decimal digit of x belongs to {0,1,6,8,9}, and flip(x) = x}|. Whenever confusing_number_ii(n) returns r, r = V(n) - F(n).
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_12 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
          r.val = (V n.val.toNat : Int) - (F n.val.toNat : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.ConfusingNumberIi.confusing_number_ii n = ok r →
            r.val = (V n.val.toNat : Int) - (F n.val.toNat : Int)) := by
    sorry

  end AegisSpec.ConfusingNumberIi
