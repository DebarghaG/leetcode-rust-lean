import Aegis.KMirror.Code.Funs

/-!
# Specifications of `Aegis.KMirror.k_mirror`

LeetCode problem `sum-of-k-mirror-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KMirror

  def baseDigits (b : Nat) (x : Nat) : List Nat :=
    if _ : b < 2 then []
    else if _ : x = 0 then []
    else x % b :: baseDigits b (x / b)
  termination_by x
  decreasing_by
    have hx : 0 < x := by omega
    have hb : 1 < b := by omega
    exact Nat.div_lt_self hx hb

  def IsPalindrome {α : Type} (l : List α) : Prop := l.reverse = l

  def IsBasePalindrome (b x : Nat) : Prop := IsPalindrome (baseDigits b x)

  def IsDecPalindrome (x : Nat) : Prop := IsBasePalindrome 10 x

  def IsKMirror (k x : Nat) : Prop := 0 < x ∧ IsDecPalindrome x ∧ IsBasePalindrome k x

  instance instDecidableIsBasePalindrome (b x : Nat) : Decidable (IsBasePalindrome b x) := by
    unfold IsBasePalindrome IsPalindrome
    infer_instance

  instance instDecidableIsDecPalindrome (x : Nat) : Decidable (IsDecPalindrome x) := by
    unfold IsDecPalindrome
    infer_instance

  instance instDecidableIsKMirror (k x : Nat) : Decidable (IsKMirror k x) := by
    unfold IsKMirror
    infer_instance

  noncomputable def countUpTo (P : Nat → Prop) (M : Nat) : Nat := by
    classical
    exact ((Finset.Icc 1 M).filter P).card

  noncomputable def sumUpTo (P : Nat → Prop) (M : Nat) : Nat := by
    classical
    exact ((Finset.Icc 1 M).filter P).sum id

  noncomputable def boundOfFirstN (P : Nat → Prop) (n : Nat) : Nat := by
    classical
    exact if h : ∃ M, countUpTo P M = n then Nat.find h else 0

  noncomputable def sumFirstN (P : Nat → Prop) (n : Nat) : Nat :=
    sumUpTo P (boundOfFirstN P n)

  noncomputable def nthSmallest (P : Nat → Prop) (i : Nat) : Nat :=
    boundOfFirstN P (i + 1)

  noncomputable def kmirrorSum (k n : Nat) : Nat := sumFirstN (IsKMirror k) n

  noncomputable def kmirrorNth (k i : Nat) : Nat := nthSmallest (IsKMirror k) i

  noncomputable def decPalindromeSum (n : Nat) : Nat :=
    sumFirstN (fun x => IsDecPalindrome x) n

  noncomputable def basePalindromeSum (k n : Nat) : Nat :=
    sumFirstN (fun x => IsBasePalindrome k x) n

  /-- Whenever k_mirror(k,n) returns a result r, r = a_1 + a_2 + ... + a_n, i.e. r is the sum of the n smallest positive k-mirror integers.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 1 <= n <= 30. For a positive integer x, x is k-mirror if the decimal representation of x (without leading zeros) is a palindrome and the base-k representation of x (without leading zeros, using digits 0 through k-1) is a palindrome. Let a_1 < a_2 < ... be all positive k-mirror integers in increasing order. -/
  theorem spec_1 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30) :
      ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
        r.val = ((kmirrorSum k.val.toNat n.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30), ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
          r.val = ((kmirrorSum k.val.toNat n.val.toNat : Nat) : Int)) := by
    sorry

  /-- For every k and n satisfying the preconditions, k_mirror(k,n) returns a result r; the call does not panic, read out of bounds, or overflow 64-bit arithmetic.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 1 <= n <= 30. -/
  theorem spec_2 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30) :
      ∃ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30), ∃ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r) := by
    sorry

  /-- Whenever k_mirror(k,n) returns r, r = n*(n+1)/2. In this range the n smallest k-mirror numbers are exactly 1,2,...,n.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 1 <= n < k. A positive integer is k-mirror when its base-10 and base-k representations (both without leading zeros) are palindromes. -/
  theorem spec_3 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val < k.val) :
      ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
        r.val = ((n.val.toNat * (n.val.toNat + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val < k.val), ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
          r.val = ((n.val.toNat * (n.val.toNat + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever k_mirror(k,n) returns r, r = (k-1)*k/2 + (k+1). Equivalently, the n smallest k-mirror numbers are 1,2,...,k-1,k+1.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 8 and n = k. A positive integer is k-mirror when its base-10 and base-k representations (both without leading zeros) are palindromes. -/
  theorem spec_4 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 8) (hn : n.val = k.val) :
      ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
        r.val = (((k.val.toNat - 1) * k.val.toNat / 2 + (k.val.toNat + 1) : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 8) (hn : n.val = k.val), ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
          r.val = (((k.val.toNat - 1) * k.val.toNat / 2 + (k.val.toNat + 1) : Nat) : Int)) := by
    sorry

  /-- Whenever k_mirror(k,n) returns r, r >= d_1 + d_2 + ... + d_n.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 1 <= n <= 30. Let d_1 < d_2 < ... be all positive integers whose decimal representation (without leading zeros) is a palindrome. Let a_1 < a_2 < ... be all positive k-mirror integers, where k-mirror means palindromic in both base 10 and base k without leading zeros. -/
  theorem spec_5 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30) :
      ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
        ((decPalindromeSum n.val.toNat : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30), ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
          ((decPalindromeSum n.val.toNat : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever k_mirror(k,n) returns r, r >= b_1 + b_2 + ... + b_n.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 1 <= n <= 30. Let b_1 < b_2 < ... be all positive integers whose base-k representation (without leading zeros) is a palindrome. Let a_1 < a_2 < ... be all positive k-mirror integers, where k-mirror means palindromic in both base 10 and base k without leading zeros. -/
  theorem spec_6 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30) :
      ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
        ((basePalindromeSum k.val.toNat n.val.toNat : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30), ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
          ((basePalindromeSum k.val.toNat n.val.toNat : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever k_mirror(k,n) returns r, there exists a positive integer M such that exactly n positive k-mirror integers are <= M, and r = sum of all positive k-mirror integers x with x <= M.
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 1 <= n <= 30. Let a_1 < a_2 < ... be all positive k-mirror integers, where k-mirror means palindromic in both base 10 and base k without leading zeros. -/
  theorem spec_7 (k n : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30) :
      ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
        ∃ M : Nat, 0 < M ∧ countUpTo (IsKMirror k.val.toNat) M = n.val.toNat ∧
          r.val = ((sumUpTo (IsKMirror k.val.toNat) M : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k n : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 1 ≤ n.val ∧ n.val ≤ 30), ∀ r : Std.I64, Aegis.KMirror.k_mirror k n = ok r →
          ∃ M : Nat, 0 < M ∧ countUpTo (IsKMirror k.val.toNat) M = n.val.toNat ∧
            r.val = ((sumUpTo (IsKMirror k.val.toNat) M : Nat) : Int)) := by
    sorry

  /-- If k_mirror(k,n) returns r_n and k_mirror(k,n-1) returns r_{n-1}, then r_n - r_{n-1} is a positive k-mirror integer (indeed it is the n-th smallest positive k-mirror integer).
    Preconditions: k and n are 64-bit machine integers with 2 <= k <= 9 and 2 <= n <= 30. A positive integer is k-mirror when its base-10 and base-k representations (both without leading zeros) are palindromes. -/
  theorem spec_8 (k n m : Std.I64)
      (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 2 ≤ n.val ∧ n.val ≤ 30) (hm : m.val = n.val - 1) :
      ∀ rn rm : Std.I64,
        Aegis.KMirror.k_mirror k n = ok rn →
        Aegis.KMirror.k_mirror k m = ok rm →
        (IsKMirror k.val.toNat (kmirrorNth k.val.toNat (n.val.toNat - 1)) ∧
          rn.val - rm.val = ((kmirrorNth k.val.toNat (n.val.toNat - 1) : Nat) : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k n m : Std.I64)
        (hk : 2 ≤ k.val ∧ k.val ≤ 9) (hn : 2 ≤ n.val ∧ n.val ≤ 30) (hm : m.val = n.val - 1), ∀ rn rm : Std.I64,
          Aegis.KMirror.k_mirror k n = ok rn →
          Aegis.KMirror.k_mirror k m = ok rm →
          (IsKMirror k.val.toNat (kmirrorNth k.val.toNat (n.val.toNat - 1)) ∧
            rn.val - rm.val = ((kmirrorNth k.val.toNat (n.val.toNat - 1) : Nat) : Int))) := by
    sorry

  end AegisSpec.KMirror
