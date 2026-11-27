import Aegis.NumberOfUniqueGoodSubsequences.Code.Funs

/-!
# Specifications of `Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences`

LeetCode problem `number-of-unique-good-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfUniqueGoodSubsequences

  def MOD : ℤ := 1000000007

  def byteZero : Aeneas.Std.U8 := 48#u8

  def byteOne : Aeneas.Std.U8 := 49#u8

  def IsBit (b : Aeneas.Std.U8) : Prop := b = byteZero ∨ b = byteOne

  def AllBits (l : List Aeneas.Std.U8) : Prop := ∀ b ∈ l, IsBit b

  def InputBits (l : List Aeneas.Std.U8) : Prop :=
    ∀ (i : ℕ) (h : i < l.length), IsBit (l[i]'(h))

  def countZerosBefore (l : List Aeneas.Std.U8) (p : ℕ) : ℕ :=
    ((Finset.range p).filter (fun i => l[i]? = some byteZero)).card

  def firstOneIdx : List Aeneas.Std.U8 → ℕ
    | [] => 0
    | b :: t => if b = byteOne then 0 else firstOneIdx t + 1

  def IsGood (l s : List Aeneas.Std.U8) : Prop :=
    s ≠ [] ∧ AllBits s ∧ s.Sublist l ∧ (s = [byteZero] ∨ s.head? = some byteOne)

  noncomputable def goodSubsequences (l : List Aeneas.Std.U8) : Finset (List Aeneas.Std.U8) := by
    classical
    exact (l.sublists.toFinset).filter (fun s => IsGood l s)

  /-- Let MOD = 1000000007. Let S be the set of all finite byte strings s such that: (1) s is nonempty; (2) every byte of s is '0' or '1'; (3) s is a subsequence of binary, meaning there exist indices 0 <= i_0 < i_1 < ... < i_{len(s)-1} < len(binary) with binary[i_j] = s[j] for every 0 <= j < len(s); and (4) either s is the one-byte string '0', or s[0] is the byte '1'. Let N = |S|. Whenever the function returns a result r, r = N mod MOD (as a nonnegative integer).
    Preconditions: 1 <= len(binary) <= 100000 and, for every i with 0 <= i < len(binary), binary[i] is the byte '0' (48) or the byte '1' (49). -/
  theorem spec_1 (binary : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        r.val = ((goodSubsequences binary.val).card : ℤ) % MOD := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          r.val = ((goodSubsequences binary.val).card : ℤ) % MOD) := by
    sorry

  /-- The function returns a result r for every binary satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: 1 <= len(binary) <= 100000 and, for every i with 0 <= i < len(binary), binary[i] is the byte '0' (48) or the byte '1' (49). -/
  theorem spec_2 (binary : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val) :
      ∃ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val), ∃ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: 1 <= len(binary) <= 100000 and, for every i with 0 <= i < len(binary), binary[i] is the byte '0' (48) or the byte '1' (49). -/
  theorem spec_3 (binary : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        0 ≤ r.val ∧ r.val < MOD := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          0 ≤ r.val ∧ r.val < MOD) := by
    sorry

  /-- Whenever the function returns a result r, r = (n * (m + 1) + (if m > 0 then 1 else 0)) mod 1000000007.
    Preconditions: The preconditions of spec_1 hold, and there exist integers n >= 0 and m >= 0 with n + m = len(binary) such that binary[i] = '1' for every 0 <= i < n and binary[i] = '0' for every n <= i < len(binary). -/
  theorem spec_4 (binary : Aeneas.Std.Slice Aeneas.Std.U8) (n m : ℕ)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val)
      (hnm : n + m = binary.val.length)
      (hones : ∀ (i : ℕ) (h : i < n), binary.val[i]'(by omega) = byteOne)
      (hzeros : ∀ (i : ℕ) (_ : n ≤ i) (h' : i < binary.val.length),
        binary.val[i]'(h') = byteZero) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        r.val = ((n : ℤ) * ((m : ℤ) + 1) + (if 0 < m then (1 : ℤ) else 0)) % MOD := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8) (n m : ℕ)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val)
        (hnm : n + m = binary.val.length)
        (hones : ∀ (i : ℕ) (h : i < n), binary.val[i]'(by omega) = byteOne)
        (hzeros : ∀ (i : ℕ) (_ : n ≤ i) (h' : i < binary.val.length),
          binary.val[i]'(h') = byteZero), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          r.val = ((n : ℤ) * ((m : ℤ) + 1) + (if 0 < m then (1 : ℤ) else 0)) % MOD) := by
    sorry

  /-- Whenever the function returns a result r, r = (b + (if a > 0 then 1 else 0)) mod 1000000007.
    Preconditions: The preconditions of spec_1 hold, and there exist integers a >= 0 and b >= 0 with a + b = len(binary) such that binary[i] = '0' for every 0 <= i < a and binary[i] = '1' for every a <= i < len(binary). -/
  theorem spec_5 (binary : Aeneas.Std.Slice Aeneas.Std.U8) (a b : ℕ)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val)
      (hab : a + b = binary.val.length)
      (hzeros : ∀ (i : ℕ) (h : i < a), binary.val[i]'(by omega) = byteZero)
      (hones : ∀ (i : ℕ) (_ : a ≤ i) (h' : i < binary.val.length),
        binary.val[i]'(h') = byteOne) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        r.val = ((b : ℤ) + (if 0 < a then (1 : ℤ) else 0)) % MOD := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8) (a b : ℕ)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val)
        (hab : a + b = binary.val.length)
        (hzeros : ∀ (i : ℕ) (h : i < a), binary.val[i]'(by omega) = byteZero)
        (hones : ∀ (i : ℕ) (_ : a ≤ i) (h' : i < binary.val.length),
          binary.val[i]'(h') = byteOne), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          r.val = ((b : ℤ) + (if 0 < a then (1 : ℤ) else 0)) % MOD) := by
    sorry

  /-- Let a be the number of indices i with 0 <= i < p and binary[i] = '0', and let b = len(binary) - p - 1. Whenever the function returns a result r, r = (b + 1 + (if a + b > 0 then 1 else 0)) mod 1000000007.
    Preconditions: The preconditions of spec_1 hold, and there is exactly one index p with 0 <= p < len(binary) such that binary[p] = '1'. -/
  theorem spec_6 (binary : Aeneas.Std.Slice Aeneas.Std.U8) (p : ℕ)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val)
      (hp : p < binary.val.length)
      (hp1 : binary.val[p]'(hp) = byteOne)
      (huniq : ∀ (i : ℕ) (h : i < binary.val.length), binary.val[i]'(h) = byteOne → i = p) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        r.val = (((binary.val.length - p - 1 : ℕ) : ℤ) + 1
            + (if 0 < countZerosBefore binary.val p + (binary.val.length - p - 1)
              then (1 : ℤ) else 0)) % MOD := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8) (p : ℕ)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val)
        (hp : p < binary.val.length)
        (hp1 : binary.val[p]'(hp) = byteOne)
        (huniq : ∀ (i : ℕ) (h : i < binary.val.length), binary.val[i]'(h) = byteOne → i = p), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          r.val = (((binary.val.length - p - 1 : ℕ) : ℤ) + 1
              + (if 0 < countZerosBefore binary.val p + (binary.val.length - p - 1)
                then (1 : ℤ) else 0)) % MOD) := by
    sorry

  /-- Let L = p and R = len(binary) - p - 1, and let n = L + R. Whenever the function returns a result r, r = (n + L * (R + 1) + 1) mod 1000000007.
    Preconditions: The preconditions of spec_1 hold, and there is exactly one index p with 0 <= p < len(binary) such that binary[p] = '0'. -/
  theorem spec_7 (binary : Aeneas.Std.Slice Aeneas.Std.U8) (p : ℕ)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val)
      (hp : p < binary.val.length)
      (hp0 : binary.val[p]'(hp) = byteZero)
      (huniq : ∀ (i : ℕ) (h : i < binary.val.length), binary.val[i]'(h) = byteZero → i = p) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        r.val = (((p : ℤ) + ((binary.val.length - p - 1 : ℕ) : ℤ))
            + (p : ℤ) * (((binary.val.length - p - 1 : ℕ) : ℤ) + 1) + 1) % MOD := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8) (p : ℕ)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val)
        (hp : p < binary.val.length)
        (hp0 : binary.val[p]'(hp) = byteZero)
        (huniq : ∀ (i : ℕ) (h : i < binary.val.length), binary.val[i]'(h) = byteZero → i = p), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          r.val = (((p : ℤ) + ((binary.val.length - p - 1 : ℕ) : ℤ))
              + (p : ℤ) * (((binary.val.length - p - 1 : ℕ) : ℤ) + 1) + 1) % MOD) := by
    sorry

  /-- Let k be the smallest index with 0 <= k < len(binary) and binary[k] = '1'; if there is no such index, let k = len(binary). Let tail be the finite byte string binary[k], binary[k+1], ..., binary[len(binary)-1] (possibly empty). For any finite byte string x, including the empty string, let C(x) be the number of distinct nonempty byte strings s over {'0','1'} that are subsequences of x and satisfy s = '0' or s[0] = '1'; set C(empty) = 0. Whenever the function returns a result r, r = (C(tail) + (if tail contains no byte '0' then 1 else 0)) mod 1000000007.
    Preconditions: The preconditions of spec_1 hold, len(binary) >= 1, and binary[0] = '0'. -/
  theorem spec_8 (binary : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
      (hbits : InputBits binary.val)
      (h0 : binary.val[0]'(by omega) = byteZero) :
      ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
        r.val = (((goodSubsequences (binary.val.drop (firstOneIdx binary.val))).card : ℤ)
            + (if byteZero ∈ binary.val.drop (firstOneIdx binary.val) then (0 : ℤ) else 1)) % MOD := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (binary : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen : 1 ≤ binary.val.length) (hlen' : binary.val.length ≤ 100000)
        (hbits : InputBits binary.val)
        (h0 : binary.val[0]'(by omega) = byteZero), ∀ r, Aegis.NumberOfUniqueGoodSubsequences.number_of_unique_good_subsequences binary = ok r →
          r.val = (((goodSubsequences (binary.val.drop (firstOneIdx binary.val))).card : ℤ)
              + (if byteZero ∈ binary.val.drop (firstOneIdx binary.val) then (0 : ℤ) else 1)) % MOD) := by
    sorry

  end AegisSpec.NumberOfUniqueGoodSubsequences
