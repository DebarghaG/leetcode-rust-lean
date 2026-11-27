import Aegis.SplitNum.Code.Funs

/-!
# Specifications of `Aegis.SplitNum.split_num`

LeetCode problem `split-with-minimum-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SplitNum

  namespace AegisSpec.SplitNum

  def decDigits : Nat → List Nat
    | 0 => []
    | n + 1 => decDigits ((n + 1) / 10) ++ [(n + 1) % 10]

  def numDigits (num : Std.I64) : List Nat := decDigits num.val.toNat

  def digValAux (acc : Nat) : List Nat → Nat
    | [] => acc
    | d :: ds => digValAux (acc * 10 + d) ds

  def digVal (t : List Nat) : Nat := digValAux 0 t

  def digitSum (t : List Nat) : Nat := t.sum

  def repunit (m : Nat) : Nat := (10 ^ m - 1) / 9

  def halfFloor (k : Nat) : Nat := k / 2

  def halfCeil (k : Nat) : Nat := (k + 1) / 2

  def nonzeroDigits (t : List Nat) : List Nat := t.filter (fun d => d != 0)

  def IsMinSplitValue (s : List Nat) (r : Int) : Prop :=
    (∀ a b : List Nat, (a ++ b).Perm s → r ≤ (digVal a : Int) + (digVal b : Int)) ∧
      ∃ a b : List Nat, (a ++ b).Perm s ∧ r = (digVal a : Int) + (digVal b : Int)

  /-- Let s be the decimal digit string of num, most significant digit first. Call a pair (a,b) of finite digit strings (each possibly empty and allowed to begin with '0') a split if a++b is a permutation of s. For a digit string t, let val(t) be the integer represented by t with leading zeros allowed, and let val(empty)=0. Then the function returns a result r such that r = min { val(a)+val(b) | (a,b) is a split }.
    Preconditions: num is an i64 with 10 <= num; thus num is positive and its decimal representation has no leading zeros. -/
  theorem spec_1 (num : Std.I64) (h : 10 ≤ num.val) :
      ∃ r : Std.I64, split_num num = ok r ∧ IsMinSplitValue (numDigits num) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∃ r : Std.I64, split_num num = ok r ∧ IsMinSplitValue (numDigits num) r.val) := by
    sorry

  /-- For every such num, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_2 (num : Std.I64) (h : 10 ≤ num.val) :
      ∃ r : Std.I64, split_num num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∃ r : Std.I64, split_num num = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exist finite digit strings a and b, both nonempty, such that a++b is a permutation of the decimal digit string s of num and r = val(a)+val(b), where val(t) is the integer represented by t with leading zeros allowed.
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_3 (num : Std.I64) (h : 10 ≤ num.val) :
      ∀ r : Std.I64, split_num num = ok r →
        ∃ a b : List Nat,
          a ≠ [] ∧ b ≠ [] ∧ (a ++ b).Perm (numDigits num) ∧
            r.val = (digVal a : Int) + (digVal b : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∀ r : Std.I64, split_num num = ok r →
          ∃ a b : List Nat,
            a ≠ [] ∧ b ≠ [] ∧ (a ++ b).Perm (numDigits num) ∧
              r.val = (digVal a : Int) + (digVal b : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of finite digit strings a,b (possibly empty, leading zeros allowed) with a++b a permutation of the decimal digit string s of num, we have r <= val(a)+val(b), where val(t) is the integer represented by t with leading zeros allowed.
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_4 (num : Std.I64) (h : 10 ≤ num.val) :
      ∀ r : Std.I64, split_num num = ok r →
        ∀ a b : List Nat, (a ++ b).Perm (numDigits num) →
          r.val ≤ (digVal a : Int) + (digVal b : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∀ r : Std.I64, split_num num = ok r →
          ∀ a b : List Nat, (a ++ b).Perm (numDigits num) →
            r.val ≤ (digVal a : Int) + (digVal b : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the sum of the decimal digits of num.
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_5 (num : Std.I64) (h : 10 ≤ num.val) :
      ∀ r : Std.I64, split_num num = ok r → (digitSum (numDigits num) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∀ r : Std.I64, split_num num = ok r → (digitSum (numDigits num) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= num.
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_6 (num : Std.I64) (h : 10 ≤ num.val) :
      ∀ r : Std.I64, split_num num = ok r → r.val ≤ num.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∀ r : Std.I64, split_num num = ok r → r.val ≤ num.val) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent modulo 9 to the sum of the decimal digits of num; equivalently, r and num have the same remainder modulo 9.
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_7 (num : Std.I64) (h : 10 ≤ num.val) :
      ∀ r : Std.I64, split_num num = ok r →
        r.val % 9 = (digitSum (numDigits num) : Int) % 9 ∧ r.val % 9 = num.val % 9 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∀ r : Std.I64, split_num num = ok r →
          r.val % 9 = (digitSum (numDigits num) : Int) % 9 ∧ r.val % 9 = num.val % 9) := by
    sorry

  /-- Whenever split_num(num) returns r and split_num(m) returns r', we have r = r'.
    Preconditions: num and m are i64 with 10 <= num and 10 <= m, and the decimal digit multiset of m equals that of num (the same count of each digit 0 through 9). -/
  theorem spec_8 (num m : Std.I64) (h : 10 ≤ num.val) (hm : 10 ≤ m.val)
      (hperm : (numDigits num).Perm (numDigits m)) :
      ∀ r r' : Std.I64, split_num num = ok r → split_num m = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num m : Std.I64) (h : 10 ≤ num.val) (hm : 10 ≤ m.val)
        (hperm : (numDigits num).Perm (numDigits m)), ∀ r r' : Std.I64, split_num num = ok r → split_num m = ok r' → r = r') := by
    sorry

  /-- The function returns a result r and r = (num div 10) + (num mod 10), i.e., the sum of the two decimal digits of num.
    Preconditions: num is an i64 with 10 <= num <= 99. -/
  theorem spec_9 (num : Std.I64) (h : 10 ≤ num.val) (h99 : num.val ≤ 99) :
      ∃ r : Std.I64, split_num num = ok r ∧ r.val = num.val / 10 + num.val % 10 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val) (h99 : num.val ≤ 99), ∃ r : Std.I64, split_num num = ok r ∧ r.val = num.val / 10 + num.val % 10) := by
    sorry

  /-- The function returns a result r and r = d.
    Preconditions: num is an i64 with 10 <= num, and the decimal digit string s of num has exactly one position i with digit(s[i]) != 0; let d = digit(s[i]). -/
  theorem spec_10 (num : Std.I64) (d : Nat) (h : 10 ≤ num.val)
      (hd : nonzeroDigits (numDigits num) = [d]) :
      ∃ r : Std.I64, split_num num = ok r ∧ r.val = (d : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64) (d : Nat) (h : 10 ≤ num.val)
        (hd : nonzeroDigits (numDigits num) = [d]), ∃ r : Std.I64, split_num num = ok r ∧ r.val = (d : Int)) := by
    sorry

  /-- The function returns a result r and r = d1 + d2.
    Preconditions: num is an i64 with 10 <= num, and the decimal digit string s of num has exactly two positions i != j with digit(s[i]) != 0; let d1 = digit(s[i]) and d2 = digit(s[j]). -/
  theorem spec_11 (num : Std.I64) (d1 d2 : Nat) (h : 10 ≤ num.val)
      (hd : nonzeroDigits (numDigits num) = [d1, d2]) :
      ∃ r : Std.I64, split_num num = ok r ∧ r.val = (d1 : Int) + (d2 : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Std.I64) (d1 d2 : Nat) (h : 10 ≤ num.val)
        (hd : nonzeroDigits (numDigits num) = [d1, d2]), ∃ r : Std.I64, split_num num = ok r ∧ r.val = (d1 : Int) + (d2 : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is strictly greater than the sum of the decimal digits of num.
    Preconditions: num is an i64 with 10 <= num, and the decimal digit string s of num has at least three positions with a nonzero digit. -/
  theorem spec_12 (num : Std.I64) (h : 10 ≤ num.val)
      (h3 : 3 ≤ (nonzeroDigits (numDigits num)).length) :
      ∀ r : Std.I64, split_num num = ok r → (digitSum (numDigits num) : Int) < r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val)
        (h3 : 3 ≤ (nonzeroDigits (numDigits num)).length), ∀ r : Std.I64, split_num num = ok r → (digitSum (numDigits num) : Int) < r.val) := by
    sorry

  /-- The function returns a result r and r = d * ( (10^(floor(k/2)) - 1)/9 + (10^(ceil(k/2)) - 1)/9 ).
    Preconditions: num is an i64 with 10 <= num, every digit of the decimal digit string s of num is the same digit d with 1 <= d <= 9, and k = len(s). -/
  theorem spec_13 (num : Std.I64) (d k : Nat) (h : 10 ≤ num.val)
      (hk : k = (numDigits num).length) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
      (hs : ∀ x ∈ numDigits num, x = d) :
      ∃ r : Std.I64, split_num num = ok r ∧
        r.val = ((d * (repunit (halfFloor k) + repunit (halfCeil k)) : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Std.I64) (d k : Nat) (h : 10 ≤ num.val)
        (hk : k = (numDigits num).length) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
        (hs : ∀ x ∈ numDigits num, x = d), ∃ r : Std.I64, split_num num = ok r ∧
          r.val = ((d * (repunit (halfFloor k) + repunit (halfCeil k)) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is even.
    Preconditions: num is an i64 with 10 <= num, and every decimal digit of num is even (0,2,4,6,8). -/
  theorem spec_14 (num : Std.I64) (h : 10 ≤ num.val)
      (heven : ∀ x ∈ numDigits num, x % 2 = 0) :
      ∀ r : Std.I64, split_num num = ok r → r.val % 2 = 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val)
        (heven : ∀ x ∈ numDigits num, x % 2 = 0), ∀ r : Std.I64, split_num num = ok r → r.val % 2 = 0) := by
    sorry

  /-- Whenever the function returns a result r, r <= (num div 10) + (num mod 10).
    Preconditions: num is an i64 with 10 <= num. -/
  theorem spec_15 (num : Std.I64) (h : 10 ≤ num.val) :
      ∀ r : Std.I64, split_num num = ok r → r.val ≤ num.val / 10 + num.val % 10 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (num : Std.I64) (h : 10 ≤ num.val), ∀ r : Std.I64, split_num num = ok r → r.val ≤ num.val / 10 + num.val % 10) := by
    sorry

  /-- Whenever the function returns a result r, r <= (10^(ceil(k/2)) - 1) + (10^(floor(k/2)) - 1).
    Preconditions: num is an i64 with 10 <= num, and k = len(s) where s is the decimal digit string of num. -/
  theorem spec_16 (num : Std.I64) (k : Nat) (h : 10 ≤ num.val)
      (hk : k = (numDigits num).length) :
      ∀ r : Std.I64, split_num num = ok r →
        r.val ≤ (((10 ^ halfCeil k - 1) + (10 ^ halfFloor k - 1) : Nat) : Int) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (num : Std.I64) (k : Nat) (h : 10 ≤ num.val)
        (hk : k = (numDigits num).length), ∀ r : Std.I64, split_num num = ok r →
          r.val ≤ (((10 ^ halfCeil k - 1) + (10 ^ halfFloor k - 1) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the decimal representation of r without leading zeros has length at most ceil(k/2) + 1.
    Preconditions: num is an i64 with 10 <= num, and k = len(s) where s is the decimal digit string of num. -/
  theorem spec_17 (num : Std.I64) (k : Nat) (h : 10 ≤ num.val)
      (hk : k = (numDigits num).length) :
      ∀ r : Std.I64, split_num num = ok r → (decDigits r.val.toNat).length ≤ halfCeil k + 1 := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (num : Std.I64) (k : Nat) (h : 10 ≤ num.val)
        (hk : k = (numDigits num).length), ∀ r : Std.I64, split_num num = ok r → (decDigits r.val.toNat).length ≤ halfCeil k + 1) := by
    sorry

  end AegisSpec.SplitNum
