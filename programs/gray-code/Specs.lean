import Aegis.GrayCode.Code.Funs

/-!
# Specifications of `Aegis.GrayCode.gray_code`

LeetCode problem `gray-code`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GrayCode

  def contents (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def nthVal (v : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ := (contents v)[i]?

  def lastVal (v : alloc.vec.Vec Std.I64) : Option ℤ := (contents v).getLast?

  def differInExactlyOneBit (a b : ℤ) : Prop := ∃ k : ℕ, a.toNat ^^^ b.toNat = 2 ^ k

  /-- The function returns a result r and all of the following hold: len(r) = 2^n; for every i with 0 <= i < len(r), 0 <= r[i] < 2^n; r[0] = 0; for every i and j with 0 <= i < j < len(r), r[i] != r[j]; for every i with 0 <= i < len(r)-1, the n-bit binary representations of r[i] and r[i+1] differ in exactly one bit; and the n-bit binary representations of r[len(r)-1] and r[0] differ in exactly one bit.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.GrayCode.gray_code n = ok r ∧
        r.val.length = 2 ^ n.val.toNat ∧
        (∀ (i : ℕ) (hi : i < r.val.length),
          0 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val < (2 : ℤ) ^ n.val.toNat) ∧
        nthVal r 0 = some 0 ∧
        (∀ (i j : ℕ) (hij : i < j) (hj : j < r.val.length),
          (r.val[i]'(Nat.lt_trans hij hj)).val ≠ (r.val[j]'hj).val) ∧
        (∀ (i : ℕ) (hi : i + 1 < r.val.length),
          differInExactlyOneBit (r.val[i]'(Nat.lt_of_succ_lt hi)).val (r.val[i + 1]'hi).val) ∧
        (0 < r.val.length ∧
          ∃ a b : ℤ, nthVal r 0 = some a ∧ lastVal r = some b ∧ differInExactlyOneBit b a) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.GrayCode.gray_code n = ok r ∧
          r.val.length = 2 ^ n.val.toNat ∧
          (∀ (i : ℕ) (hi : i < r.val.length),
            0 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val < (2 : ℤ) ^ n.val.toNat) ∧
          nthVal r 0 = some 0 ∧
          (∀ (i j : ℕ) (hij : i < j) (hj : j < r.val.length),
            (r.val[i]'(Nat.lt_trans hij hj)).val ≠ (r.val[j]'hj).val) ∧
          (∀ (i : ℕ) (hi : i + 1 < r.val.length),
            differInExactlyOneBit (r.val[i]'(Nat.lt_of_succ_lt hi)).val (r.val[i + 1]'hi).val) ∧
          (0 < r.val.length ∧
            ∃ a b : ℤ, nthVal r 0 = some a ∧ lastVal r = some b ∧ differInExactlyOneBit b a)) := by
    sorry

  /-- The function returns a result (it does not fail).
    Preconditions: 1 <= n <= 16. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.GrayCode.gray_code n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16), ∃ r : alloc.vec.Vec Std.I64, Aegis.GrayCode.gray_code n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2^n.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      r.val.length = 2 ^ n.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), r.val.length = 2 ^ n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i].
    Preconditions: 1 <= n <= 16. -/
  theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      ∀ (i : ℕ) (hi : i < r.val.length), 0 ≤ (r.val[i]'hi).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), ∀ (i : ℕ) (hi : i < r.val.length), 0 ≤ (r.val[i]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] < 2^n (equivalently r[i] <= 2^n - 1).
    Preconditions: 1 <= n <= 16. -/
  theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      ∀ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val < (2 : ℤ) ^ n.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), ∀ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val < (2 : ℤ) ^ n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r is non-empty and r[0] = 0.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      0 < r.val.length ∧ nthVal r 0 = some 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), 0 < r.val.length ∧ nthVal r 0 = some 0) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: 1 <= n <= 16. -/
  theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      ∀ (i j : ℕ) (hij : i < j) (hj : j < r.val.length),
        (r.val[i]'(Nat.lt_trans hij hj)).val ≠ (r.val[j]'hj).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), ∀ (i j : ℕ) (hij : i < j) (hj : j < r.val.length),
          (r.val[i]'(Nat.lt_trans hij hj)).val ≠ (r.val[j]'hj).val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v with 0 <= v < 2^n, there exists an index i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      ∀ v : ℤ, 0 ≤ v → v < (2 : ℤ) ^ n.val.toNat →
        ∃ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val = v := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), ∀ v : ℤ, 0 ≤ v → v < (2 : ℤ) ^ n.val.toNat →
          ∃ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val = v) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r)-1, the n-bit binary representations of r[i] and r[i+1] differ in exactly one bit; equivalently, (r[i] XOR r[i+1]) has exactly one bit set.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      ∀ (i : ℕ) (hi : i + 1 < r.val.length),
        differInExactlyOneBit (r.val[i]'(Nat.lt_of_succ_lt hi)).val (r.val[i + 1]'hi).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), ∀ (i : ℕ) (hi : i + 1 < r.val.length),
          differInExactlyOneBit (r.val[i]'(Nat.lt_of_succ_lt hi)).val (r.val[i + 1]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r, r is non-empty and the n-bit binary representations of r[len(r)-1] and r[0] differ in exactly one bit; equivalently, (r[len(r)-1] XOR r[0]) has exactly one bit set.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      0 < r.val.length ∧
        ∃ a b : ℤ, nthVal r 0 = some a ∧ lastVal r = some b ∧ differInExactlyOneBit b a := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), 0 < r.val.length ∧
          ∃ a b : ℤ, nthVal r 0 = some a ∧ lastVal r = some b ∧ differInExactlyOneBit b a) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2, r[0] = 0, and r[1] = 1; that is, r = [0,1].
    Preconditions: n = 1 (which satisfies 1 <= n <= 16). -/
  theorem spec_11 (n : Std.I64) (hn : n.val = 1)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      r.val.length = 2 ∧ nthVal r 0 = some 0 ∧ nthVal r 1 = some 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), r.val.length = 2 ∧ nthVal r 0 = some 0 ∧ nthVal r 1 = some 1) := by
    sorry

  /-- Whenever the function returns a result r, r is either [0,1,3,2] or [0,2,3,1].
    Preconditions: n = 2 (which satisfies 1 <= n <= 16). -/
  theorem spec_12 (n : Std.I64) (hn : n.val = 2)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      contents r = [0, 1, 3, 2] ∨ contents r = [0, 2, 3, 1] := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), contents r = [0, 1, 3, 2] ∨ contents r = [0, 2, 3, 1]) := by
    sorry

  /-- Whenever the function returns a result r, r is non-empty and there exists an integer k with 0 <= k < n such that r[len(r)-1] = 2^k.
    Preconditions: 1 <= n <= 16. -/
  theorem spec_13 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r) :
      0 < r.val.length ∧ ∃ k : ℕ, (k : ℤ) < n.val ∧ lastVal r = some ((2 : ℤ) ^ k) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 16)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.GrayCode.gray_code n = ok r), 0 < r.val.length ∧ ∃ k : ℕ, (k : ℤ) < n.val ∧ lastVal r = some ((2 : ℤ) ^ k)) := by
    sorry

  end AegisSpec.GrayCode
