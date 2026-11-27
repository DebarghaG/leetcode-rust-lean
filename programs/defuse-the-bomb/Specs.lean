import Aegis.Decrypt.Code.Funs

/-!
# Specifications of `Aegis.Decrypt.decrypt`

LeetCode problem `defuse-the-bomb`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Decrypt

  open Aegis.Decrypt (decrypt)

  def codeElem (code : Slice I64) (i : Nat) : Int := (code.val.getD i 0#i64).val

  def outElem (r : alloc.vec.Vec I64) (i : Nat) : Int := (r.val.getD i 0#i64).val

  def modNat (a : Int) (n : Nat) : Nat := (a % (n : Int)).toNat

  /-- The function returns a result r (it does not fail) and len(r) = n. For every i with 0 <= i < n: if k > 0, then r[i] = sum_{j=1}^{k} code[(i+j) mod n]; if k < 0, then r[i] = sum_{j=1}^{-k} code[(i-j) mod n]; if k = 0, then r[i] = 0. Here 'mod n' denotes the unique remainder in {0, 1, ..., n-1}.
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; and -n <= k <= n. This includes the original stated range -(n-1) <= k <= n-1 and also the listed test cases with k = n or k = -n. -/
  theorem spec_1 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) :
      ∃ r : alloc.vec.Vec I64,
        decrypt code k = ok r ∧
        r.val.length = code.val.length ∧
        (∀ i, i < code.val.length →
          (0 < k.val →
            outElem r i = ∑ j ∈ Finset.Icc 1 k.val.toNat,
              codeElem code (modNat ((i : Int) + (j : Int)) code.val.length)) ∧
          (k.val < 0 →
            outElem r i = ∑ j ∈ Finset.Icc 1 (-k.val).toNat,
              codeElem code (modNat ((i : Int) - (j : Int)) code.val.length)) ∧
          (k.val = 0 → outElem r i = 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)), ∃ r : alloc.vec.Vec I64,
          decrypt code k = ok r ∧
          r.val.length = code.val.length ∧
          (∀ i, i < code.val.length →
            (0 < k.val →
              outElem r i = ∑ j ∈ Finset.Icc 1 k.val.toNat,
                codeElem code (modNat ((i : Int) + (j : Int)) code.val.length)) ∧
            (k.val < 0 →
              outElem r i = ∑ j ∈ Finset.Icc 1 (-k.val).toNat,
                codeElem code (modNat ((i : Int) - (j : Int)) code.val.length)) ∧
            (k.val = 0 → outElem r i = 0))) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; and -n <= k <= n. -/
  theorem spec_2 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) :
      ∃ r : alloc.vec.Vec I64, decrypt code k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)), ∃ r : alloc.vec.Vec I64, decrypt code k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(code).
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; and -n <= k <= n. -/
  theorem spec_3 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) :
      ∀ r : alloc.vec.Vec I64, decrypt code k = ok r → r.val.length = code.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)), ∀ r : alloc.vec.Vec I64, decrypt code k = ok r → r.val.length = code.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, |k| <= r[i] <= 100 * |k|, where |k| is the absolute value of k.
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; and -n <= k <= n. -/
  theorem spec_4 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) :
      ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
        ∀ i, i < code.val.length →
          |k.val| ≤ outElem r i ∧ outElem r i ≤ 100 * |k.val| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)), ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
          ∀ i, i < code.val.length →
            |k.val| ≤ outElem r i ∧ outElem r i ≤ 100 * |k.val|) := by
    sorry

  /-- Whenever the function returns a result r, sum_{i=0}^{n-1} r[i] = |k| * sum_{i=0}^{n-1} code[i].
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; and -n <= k <= n. -/
  theorem spec_5 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) :
      ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
        (∑ i ∈ Finset.range code.val.length, outElem r i) =
          |k.val| * ∑ i ∈ Finset.range code.val.length, codeElem code i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)), ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
          (∑ i ∈ Finset.range code.val.length, outElem r i) =
            |k.val| * ∑ i ∈ Finset.range code.val.length, codeElem code i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[(i+1) mod n] - r[i] = code[(i+k+1) mod n] - code[(i+1) mod n].
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; -n <= k <= n; and k > 0. -/
  theorem spec_6 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) (hk_pos : 0 < k.val) :
      ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
        ∀ i, i < code.val.length →
          outElem r (modNat ((i : Int) + 1) code.val.length) - outElem r i =
            codeElem code (modNat ((i : Int) + k.val + 1) code.val.length) -
              codeElem code (modNat ((i : Int) + 1) code.val.length) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)) (hk_pos : 0 < k.val), ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
          ∀ i, i < code.val.length →
            outElem r (modNat ((i : Int) + 1) code.val.length) - outElem r i =
              codeElem code (modNat ((i : Int) + k.val + 1) code.val.length) -
                codeElem code (modNat ((i : Int) + 1) code.val.length)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[(i+1) mod n] - r[i] = code[i] - code[(i+k) mod n].
    Preconditions: Let n = len(code). Assume 1 <= n <= 100; for every i with 0 <= i < n, 1 <= code[i] <= 100; -n <= k <= n; and k < 0. -/
  theorem spec_7 (code : Slice I64) (k : I64)
      (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
      (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
      (hk_lo : -(code.val.length : Int) ≤ k.val)
      (hk_hi : k.val ≤ (code.val.length : Int)) (hk_neg : k.val < 0) :
      ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
        ∀ i, i < code.val.length →
          outElem r (modNat ((i : Int) + 1) code.val.length) - outElem r i =
            codeElem code i - codeElem code (modNat ((i : Int) + k.val) code.val.length) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (code : Slice I64) (k : I64)
        (hn_pos : 1 ≤ code.val.length) (hn_le : code.val.length ≤ 100)
        (hcode : ∀ i, i < code.val.length → 1 ≤ codeElem code i ∧ codeElem code i ≤ 100)
        (hk_lo : -(code.val.length : Int) ≤ k.val)
        (hk_hi : k.val ≤ (code.val.length : Int)) (hk_neg : k.val < 0), ∀ r : alloc.vec.Vec I64, decrypt code k = ok r →
          ∀ i, i < code.val.length →
            outElem r (modNat ((i : Int) + 1) code.val.length) - outElem r i =
              codeElem code i - codeElem code (modNat ((i : Int) + k.val) code.val.length)) := by
    sorry

  end AegisSpec.Decrypt
