import Aegis.Compress.Code.Funs

/-!
# Specifications of `Aegis.Compress.compress`

LeetCode problem `string-compression`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Compress

def bytes (chars : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  chars.val.map alloc.vec.Vec.val

def len (chars : Slice (alloc.vec.Vec Std.U8)) : Nat := chars.val.length

def elem (chars : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
  (bytes chars).getD i []

def digits (g : Nat) : Nat := (Nat.toDigits 10 g).length

def encLen (g : Nat) : Nat := if g = 1 then 1 else 1 + digits g

def runLengthsFrom {α : Type} [DecidableEq α] (a : α) (k : Nat) : List α → List Nat
  | [] => [k]
  | b :: rest =>
    if b = a then runLengthsFrom a (k + 1) rest
    else k :: runLengthsFrom b 1 rest

def runLengths {α : Type} [DecidableEq α] : List α → List Nat
  | [] => []
  | a :: rest => runLengthsFrom a 1 rest

def groupLens (chars : Slice (alloc.vec.Vec Std.U8)) : List Nat := runLengths (bytes chars)

abbrev IsGroupStart (chars : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Prop :=
  i < len chars ∧ (i = 0 ∨ elem chars i ≠ elem chars (i - 1))

def numGroups (chars : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  ((List.range (len chars)).filter (fun i => decide (IsGroupStart chars i))).length

def numLongGroups (chars : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (groupLens chars).countP (fun g => decide (2 ≤ g))

def encSize (chars : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  ((groupLens chars).map encLen).sum

/-- Let n = len(chars). Call an index i a group start if 0 <= i < n and (i = 0 or chars[i] != chars[i-1]). For a group start i, let next(i) be the least j with i < j <= n such that j = n or chars[j] != chars[j-1], and let g_i = next(i) - i. Let digits(g) be the number of decimal digits of g for g >= 1. The function returns Result.ok ret for some Std.I64 ret, and ret = the sum over all group starts i of (1 if g_i = 1 else 1 + digits(g_i)).
  Preconditions: 1 <= len(chars) <= 2000, and for every i with 0 <= i < len(chars), len(chars[i]) = 1 (each element is a one-byte character). -/
theorem spec_1 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1) :
    ∃ r : Std.I64, Aegis.Compress.compress chars = ok r ∧ r.val = (encSize chars : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1), ∃ r : Std.I64, Aegis.Compress.compress chars = ok r ∧ r.val = (encSize chars : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the value of compress chars is Result.ok ret for some Std.I64 ret; the function does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: 1 <= len(chars) <= 2000, and for every i with 0 <= i < len(chars), len(chars[i]) = 1. -/
theorem spec_2 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1) :
    ∃ r : Std.I64, Aegis.Compress.compress chars = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1), ∃ r : Std.I64, Aegis.Compress.compress chars = ok r) := by
  sorry

/-- Whenever compress chars returns Result.ok ret, 1 <= ret <= len(chars).
  Preconditions: 1 <= len(chars) <= 2000, and for every i with 0 <= i < len(chars), len(chars[i]) = 1. -/
theorem spec_3 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1) :
    ∀ r : Std.I64, Aegis.Compress.compress chars = ok r →
      1 ≤ r.val ∧ r.val ≤ (len chars : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1), ∀ r : Std.I64, Aegis.Compress.compress chars = ok r →
      1 ≤ r.val ∧ r.val ≤ (len chars : ℤ)) := by
  sorry

/-- Let G be the number of maximal contiguous groups of equal elements in chars; equivalently, G is the number of indices i with 0 <= i < len(chars) and (i = 0 or chars[i] != chars[i-1]). Whenever compress chars returns Result.ok ret, ret >= G.
  Preconditions: 1 <= len(chars) <= 2000, and for every i with 0 <= i < len(chars), len(chars[i]) = 1. -/
theorem spec_4 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1) :
    ∀ r : Std.I64, Aegis.Compress.compress chars = ok r → (numGroups chars : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1), ∀ r : Std.I64, Aegis.Compress.compress chars = ok r → (numGroups chars : ℤ) ≤ r.val) := by
  sorry

/-- Whenever compress chars returns Result.ok ret, ret = len(chars).
  Preconditions: 1 <= len(chars) <= 2000, for every i with 0 <= i < len(chars), len(chars[i]) = 1, and for every i with 0 <= i < len(chars)-1, chars[i] != chars[i+1]. -/
theorem spec_5 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hne : ∀ i, i + 1 < len chars → elem chars i ≠ elem chars (i + 1)) :
    ∀ r : Std.I64, Aegis.Compress.compress chars = ok r → r.val = (len chars : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hne : ∀ i, i + 1 < len chars → elem chars i ≠ elem chars (i + 1)), ∀ r : Std.I64, Aegis.Compress.compress chars = ok r → r.val = (len chars : ℤ)) := by
  sorry

/-- Let n = len(chars). Whenever compress chars returns Result.ok ret, ret = 1 if n = 1, and ret = 1 + digits(n) if n >= 2, where digits(n) is the number of decimal digits of n.
  Preconditions: 1 <= len(chars) <= 2000, for every i with 0 <= i < len(chars), len(chars[i]) = 1, and for every i with 0 <= i < len(chars)-1, chars[i] = chars[i+1]. -/
theorem spec_6 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (heq : ∀ i, i + 1 < len chars → elem chars i = elem chars (i + 1)) :
    ∀ r : Std.I64, Aegis.Compress.compress chars = ok r →
      r.val = (encLen (len chars) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (heq : ∀ i, i + 1 < len chars → elem chars i = elem chars (i + 1)), ∀ r : Std.I64, Aegis.Compress.compress chars = ok r →
      r.val = (encLen (len chars) : ℤ)) := by
  sorry

/-- Whenever compress chars returns Result.ok ret, ret < len(chars).
  Preconditions: 1 <= len(chars) <= 2000, for every i with 0 <= i < len(chars), len(chars[i]) = 1, and there exists i with i + 2 < len(chars) such that chars[i] = chars[i+1] and chars[i+1] = chars[i+2]. -/
theorem spec_7 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hrep : ∃ i, i + 2 < len chars ∧ elem chars i = elem chars (i + 1) ∧
      elem chars (i + 1) = elem chars (i + 2)) :
    ∀ r : Std.I64, Aegis.Compress.compress chars = ok r → r.val < (len chars : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hrep : ∃ i, i + 2 < len chars ∧ elem chars i = elem chars (i + 1) ∧
      elem chars (i + 1) = elem chars (i + 2)), ∀ r : Std.I64, Aegis.Compress.compress chars = ok r → r.val < (len chars : ℤ)) := by
  sorry

/-- Let G be the number of maximal contiguous groups of equal elements in chars, and let H be the number of those groups whose length is at least 2. Whenever compress chars returns Result.ok ret, ret = G + H.
  Preconditions: 1 <= len(chars) <= 2000, for every i with 0 <= i < len(chars), len(chars[i]) = 1, and for every i with i + 9 < len(chars), not all of chars[i], chars[i+1], ..., chars[i+9] are equal. -/
theorem spec_8 (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hshort : ∀ i, i + 9 < len chars → ¬ (∀ k, k ≤ 9 → elem chars (i + k) = elem chars i)) :
    ∀ r : Std.I64, Aegis.Compress.compress chars = ok r →
      r.val = ((numGroups chars + numLongGroups chars : Nat) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (chars : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hshort : ∀ i, i + 9 < len chars → ¬ (∀ k, k ≤ 9 → elem chars (i + k) = elem chars i)), ∀ r : Std.I64, Aegis.Compress.compress chars = ok r →
      r.val = ((numGroups chars + numLongGroups chars : Nat) : ℤ)) := by
  sorry

/-- If for every i with 0 <= i < n-1, (chars[i] = chars[i+1]) iff (other[i] = other[i+1]), then whenever compress chars returns Result.ok ret1 and compress other returns Result.ok ret2, ret1 = ret2.
  Preconditions: Both chars and other satisfy 1 <= len <= 2000 and have all elements of length 1, and len(chars) = len(other) = n. -/
theorem spec_9 (chars other : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hlo' : 1 ≤ len other) (hhi' : len other ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hunit' : ∀ i, i < len other → (elem other i).length = 1)
    (hlen : len chars = len other)
    (hsame : ∀ i, i + 1 < len chars →
      (elem chars i = elem chars (i + 1) ↔ elem other i = elem other (i + 1))) :
    ∀ r1 r2 : Std.I64, Aegis.Compress.compress chars = ok r1 →
      Aegis.Compress.compress other = ok r2 → r1 = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (chars other : Slice (alloc.vec.Vec Std.U8))
    (hlo : 1 ≤ len chars) (hhi : len chars ≤ 2000)
    (hlo' : 1 ≤ len other) (hhi' : len other ≤ 2000)
    (hunit : ∀ i, i < len chars → (elem chars i).length = 1)
    (hunit' : ∀ i, i < len other → (elem other i).length = 1)
    (hlen : len chars = len other)
    (hsame : ∀ i, i + 1 < len chars →
      (elem chars i = elem chars (i + 1) ↔ elem other i = elem other (i + 1))), ∀ r1 r2 : Std.I64, Aegis.Compress.compress chars = ok r1 →
      Aegis.Compress.compress other = ok r2 → r1 = r2) := by
  sorry

end AegisSpec.Compress
