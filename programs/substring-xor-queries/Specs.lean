import Aegis.SubstringXorQueries.Code.Funs

/-!
# Specifications of `Aegis.SubstringXorQueries.substring_xor_queries`

LeetCode problem `substring-xor-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubstringXorQueries

open Aegis.SubstringXorQueries

def byteAt (s : Slice Std.U8) (k : Nat) : Nat := ((s.val[k]?).map (·.val)).getD 0

def xorInt (a b : Int) : Int := ((Nat.xor a.toNat b.toNat : Nat) : Int)

def V (s : Slice Std.U8) (l r : Nat) : Int :=
  ∑ k ∈ Finset.Icc l r, ((byteAt s k : Int) - 48) * 2 ^ (r - k)

def occurs (s : Slice Std.U8) (b : Nat) : Prop := ∃ k, k < s.val.length ∧ byteAt s k = b

def IsFirstOccurrence (s : Slice Std.U8) (b j : Nat) : Prop :=
  j < s.val.length ∧ byteAt s j = b ∧ ∀ j', j' < j → byteAt s j' ≠ b

def answerRow (out : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Nat) : Option (List Int) :=
  (out.val[i]?).map (fun row => row.val.map (·.val))

def answerRowLength (out : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Nat) : Option Nat :=
  (out.val[i]?).map (fun row => row.val.length)

def queryContents (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  ((queries.val[i]?).map (fun v => v.val.map (·.val))).getD []

def queryFirst (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  (queryContents queries i).getD 0 0

def querySecond (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  (queryContents queries i).getD 1 0

def queryTarget (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  xorInt (queryFirst queries i) (querySecond queries i)

def HasValue (s : Slice Std.U8) (t : Int) : Prop :=
  ∃ l r, l ≤ r ∧ r < s.val.length ∧ V s l r = t

/-- Whenever the function returns a result out, out is the complete answer: len(out) = len(queries), each out[i] has length 2, and for every i with 0 <= i < len(queries), let T_i = queries[i][0] XOR queries[i][1] (bitwise XOR of nonnegative integers) and let V(l,r) = sum_{k=l}^{r} (s[k]-48) * 2^{r-k}. If there exist integers l,r with 0 <= l <= r < len(s) and V(l,r) = T_i, then out[i] = [L,R] where 0 <= L <= R < len(s), V(L,R) = T_i, and for every l,r with 0 <= l <= r < len(s) and V(l,r) = T_i, either R-L+1 < r-l+1, or R-L+1 = r-l+1 and L <= l. If no such l,r exist, then out[i] = [-1,-1].
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_1 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    out.val.length = queries.val.length ∧
      (∀ i, i < queries.val.length →
        answerRowLength out i = some 2 ∧
          (HasValue s (queryTarget queries i) →
            ∀ L R, answerRow out i = some [L, R] →
              0 ≤ L ∧ L ≤ R ∧ R < (s.val.length : Int) ∧
                V s L.toNat R.toNat = queryTarget queries i ∧
                ∀ l r, l ≤ r → r < s.val.length → V s l r = queryTarget queries i →
                  R - L + 1 < (r : Int) - (l : Int) + 1 ∨
                    (R - L + 1 = (r : Int) - (l : Int) + 1 ∧ L ≤ (l : Int))) ∧
          (¬ HasValue s (queryTarget queries i) → answerRow out i = some [-1, -1])) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), out.val.length = queries.val.length ∧
      (∀ i, i < queries.val.length →
        answerRowLength out i = some 2 ∧
          (HasValue s (queryTarget queries i) →
            ∀ L R, answerRow out i = some [L, R] →
              0 ≤ L ∧ L ≤ R ∧ R < (s.val.length : Int) ∧
                V s L.toNat R.toNat = queryTarget queries i ∧
                ∀ l r, l ≤ r → r < s.val.length → V s l r = queryTarget queries i →
                  R - L + 1 < (r : Int) - (l : Int) + 1 ∨
                    (R - L + 1 = (r : Int) - (l : Int) + 1 ∧ L ≤ (l : Int))) ∧
          (¬ HasValue s (queryTarget queries i) → answerRow out i = some [-1, -1]))) := by
  sorry

/-- Whenever the function returns a result out, len(out) = len(queries) and for every i with 0 <= i < len(queries), len(out[i]) = 2.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_2 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    out.val.length = queries.val.length ∧
      ∀ i, i < queries.val.length → answerRowLength out i = some 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), out.val.length = queries.val.length ∧
      ∀ i, i < queries.val.length → answerRowLength out i = some 2) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] is not the vector [-1,-1], then out[i][0] and out[i][1] are nonnegative, out[i][0] <= out[i][1], and out[i][1] < len(s).
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_3 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        0 ≤ L ∧ L ≤ R ∧ R < (s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        0 ≤ L ∧ L ≤ R ∧ R < (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), let T_i = queries[i][0] XOR queries[i][1] and V(l,r) = sum_{k=l}^{r} (s[k]-48) * 2^{r-k}. Then out[i] = [-1,-1] if and only if there do not exist integers l,r with 0 <= l <= r < len(s) and V(l,r) = T_i.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_4 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      (answerRow out i = some [-1, -1] ↔ ¬ HasValue s (queryTarget queries i)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      (answerRow out i = some [-1, -1] ↔ ¬ HasValue s (queryTarget queries i))) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] = [L,R] and out[i] is not [-1,-1], then 0 <= L <= R < len(s) and V(L,R) XOR queries[i][0] = queries[i][1], where V(L,R) = sum_{k=L}^{R} (s[k]-48) * 2^{R-k}.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_5 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        0 ≤ L ∧ L ≤ R ∧ R < (s.val.length : Int) ∧
          xorInt (V s L.toNat R.toNat) (queryFirst queries i) = querySecond queries i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        0 ≤ L ∧ L ≤ R ∧ R < (s.val.length : Int) ∧
          xorInt (V s L.toNat R.toNat) (queryFirst queries i) = querySecond queries i) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] = [L,R] and out[i] is not [-1,-1], then for every l,r with 0 <= l <= r < len(s) and V(l,r) = (queries[i][0] XOR queries[i][1]), we have R-L+1 <= r-l+1, where V(l,r) = sum_{k=l}^{r} (s[k]-48) * 2^{r-k}.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_6 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        ∀ l r, l ≤ r → r < s.val.length → V s l r = queryTarget queries i →
          R - L + 1 ≤ (r : Int) - (l : Int) + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        ∀ l r, l ≤ r → r < s.val.length → V s l r = queryTarget queries i →
          R - L + 1 ≤ (r : Int) - (l : Int) + 1) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] = [L,R] and out[i] is not [-1,-1], then for every l,r with 0 <= l <= r < len(s), V(l,r) = (queries[i][0] XOR queries[i][1]), and r-l+1 = R-L+1, we have L <= l, where V(l,r) = sum_{k=l}^{r} (s[k]-48) * 2^{r-k}.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_7 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        ∀ l r, l ≤ r → r < s.val.length → V s l r = queryTarget queries i →
          (r : Int) - (l : Int) + 1 = R - L + 1 → L ≤ (l : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        ∀ l r, l ≤ r → r < s.val.length → V s l r = queryTarget queries i →
          (r : Int) - (l : Int) + 1 = R - L + 1 → L ≤ (l : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: len(s) >= 1 and len(s) <= 10^4; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1 and len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_8 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_size : s.val.length ≤ 10 ^ 4)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_size : queries.val.length ≤ 10 ^ 5)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9) :
    ∃ out, substring_xor_queries s queries = ok out := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_size : s.val.length ≤ 10 ^ 4)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_size : queries.val.length ≤ 10 ^ 5)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9), ∃ out, substring_xor_queries s queries = ok out) := by
  sorry

/-- Whenever the function returns a result out, for every i,j with 0 <= i,j < len(queries), if (queries[i][0] XOR queries[i][1]) = (queries[j][0] XOR queries[j][1]), then out[i] = out[j].
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_9 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length → ∀ j, j < queries.val.length →
      queryTarget queries i = queryTarget queries j → answerRow out i = answerRow out j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length → ∀ j, j < queries.val.length →
      queryTarget queries i = queryTarget queries j → answerRow out i = answerRow out j) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] = [L,R] and out[i] is not [-1,-1] and L < R, then s[L] = 49, the byte '1'.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_10 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) → L < R →
        byteAt s L.toNat = 49 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) → L < R →
        byteAt s L.toNat = 49) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] = [L,R] and out[i] is not [-1,-1], then R-L+1 <= 30.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_11 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        R - L + 1 ≤ 30 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        R - L + 1 ≤ 30) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), if out[i] = [L,R] and out[i] is not [-1,-1], then V(L,R) < 2^30, where V(L,R) = sum_{k=L}^{R} (s[k]-48) * 2^{R-k}.
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_12 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        V s L.toNat R.toNat < 2 ^ 30 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      ∀ L R, answerRow out i = some [L, R] → (L, R) ≠ ((-1 : Int), (-1 : Int)) →
        V s L.toNat R.toNat < 2 ^ 30) := by
  sorry

/-- Whenever the function returns a result out, for every i with 0 <= i < len(queries), let T_i = queries[i][0] XOR queries[i][1]. If T_i = 0 and s contains a byte 48 ('0'), then out[i] = [j,j] where j is the smallest index with 0 <= j < len(s) and s[j] = 48; if T_i = 0 and s contains no 48, then out[i] = [-1,-1]. If T_i = 1 and s contains a byte 49 ('1'), then out[i] = [j,j] where j is the smallest index with 0 <= j < len(s) and s[j] = 49; if T_i = 1 and s contains no 49, then out[i] = [-1,-1].
  Preconditions: len(s) >= 1; every byte s[k] with 0 <= k < len(s) is 48 ('0') or 49 ('1'); len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] <= 10^9, and 0 <= queries[i][1] <= 10^9. -/
theorem spec_13 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out) :
    ∀ i, i < queries.val.length →
      (queryTarget queries i = 0 ∧ occurs s 48 →
          ∃ j, IsFirstOccurrence s 48 j ∧ answerRow out i = some [(j : Int), (j : Int)]) ∧
        (queryTarget queries i = 0 ∧ ¬ occurs s 48 → answerRow out i = some [-1, -1]) ∧
        (queryTarget queries i = 1 ∧ occurs s 49 →
          ∃ j, IsFirstOccurrence s 49 j ∧ answerRow out i = some [(j : Int), (j : Int)]) ∧
        (queryTarget queries i = 1 ∧ ¬ occurs s 49 → answerRow out i = some [-1, -1]) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
    (hs_len : 1 ≤ s.val.length)
    (hs_bits : ∀ k, k < s.val.length → byteAt s k = 48 ∨ byteAt s k = 49)
    (hq_len : 1 ≤ queries.val.length)
    (hq_shape : ∀ i, i < queries.val.length →
      (queries.val[i]?).map (fun v => v.val.length) = some 2)
    (hq_bounds : ∀ i, i < queries.val.length →
      0 ≤ queryFirst queries i ∧ queryFirst queries i ≤ 10 ^ 9 ∧
      0 ≤ querySecond queries i ∧ querySecond queries i ≤ 10 ^ 9)
    (out : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hout : substring_xor_queries s queries = ok out), ∀ i, i < queries.val.length →
      (queryTarget queries i = 0 ∧ occurs s 48 →
          ∃ j, IsFirstOccurrence s 48 j ∧ answerRow out i = some [(j : Int), (j : Int)]) ∧
        (queryTarget queries i = 0 ∧ ¬ occurs s 48 → answerRow out i = some [-1, -1]) ∧
        (queryTarget queries i = 1 ∧ occurs s 49 →
          ∃ j, IsFirstOccurrence s 49 j ∧ answerRow out i = some [(j : Int), (j : Int)]) ∧
        (queryTarget queries i = 1 ∧ ¬ occurs s 49 → answerRow out i = some [-1, -1])) := by
  sorry

end AegisSpec.SubstringXorQueries
