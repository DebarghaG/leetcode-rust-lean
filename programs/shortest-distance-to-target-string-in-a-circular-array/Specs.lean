import Aegis.ClosestTarget.Code.Funs

/-!
# Specifications of `Aegis.ClosestTarget.closest_target`

LeetCode problem `shortest-distance-to-target-string-in-a-circular-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ClosestTarget

def isAsciiLower (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def allBytesLower (l : List Std.U8) : Prop := ∀ b ∈ l, isAsciiLower b

def wordBytes (words : Slice (alloc.vec.Vec Std.U8)) (j : Nat) : Option (List Std.U8) :=
  (words.val[j]?).map fun w => w.val

def occursAt (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (j : Nat) : Prop :=
  j < words.val.length ∧ wordBytes words j = some target.val

def absDiff (start : Int) (j : Nat) : Nat := ((j : Int) - start).natAbs

def circDist (n : Nat) (start : Int) (j : Nat) : Nat :=
  min (absDiff start j) (n - absDiff start j)

/-- Whenever the function returns a result r, the following holds. If there is no index j with 0 <= j < n such that the byte sequence words[j] equals the byte sequence target, then r = -1. If there is at least one such index, then r is the minimum circular distance from startIndex to an occurrence of target: r >= 0, for every such j we have r <= min(|j - startIndex|, n - |j - startIndex|), and there exists such a j with r = min(|j - startIndex|, n - |j - startIndex|), where |j - startIndex| denotes the ordinary absolute difference.
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_1
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        ((¬ ∃ j, occursAt words target j) → r.val = -1) ∧
        ((∃ j, occursAt words target j) →
          0 ≤ r.val ∧
          (∀ j, occursAt words target j →
            r.val ≤ (circDist n startIndex.val j : Int)) ∧
          (∃ j, occursAt words target j ∧ r.val = (circDist n startIndex.val j : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        ((¬ ∃ j, occursAt words target j) → r.val = -1) ∧
        ((∃ j, occursAt words target j) →
          0 ≤ r.val ∧
          (∀ j, occursAt words target j →
            r.val ≤ (circDist n startIndex.val j : Int)) ∧
          (∃ j, occursAt words target j ∧ r.val = (circDist n startIndex.val j : Int)))) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_2
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∃ r : Std.I64, Aegis.ClosestTarget.closest_target words target startIndex = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∃ r : Std.I64, Aegis.ClosestTarget.closest_target words target startIndex = ok r) := by
  sorry

/-- Whenever the function returns a result r, if there is no index j with 0 <= j < n such that the byte sequence words[j] equals the byte sequence target, then r = -1.
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_3
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (¬ ∃ j, occursAt words target j) → r.val = -1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (¬ ∃ j, occursAt words target j) → r.val = -1) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index j with 0 <= j < n such that the byte sequence words[j] equals the byte sequence target, then r <= floor(n / 2).
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_4
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (∃ j, occursAt words target j) → r.val ≤ ((n / 2 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (∃ j, occursAt words target j) → r.val ≤ ((n / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if the byte sequence words[startIndex] equals the byte sequence target.
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_5
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (r.val = 0 ↔ wordBytes words startIndex.val.toNat = some target.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (r.val = 0 ↔ wordBytes words startIndex.val.toNat = some target.val)) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index j with 0 <= j < n such that the byte sequence words[j] equals the byte sequence target, then for every such j, r <= min(|j - startIndex|, n - |j - startIndex|), where |j - startIndex| is the ordinary absolute difference.
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_6
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (∃ j, occursAt words target j) →
          ∀ j, occursAt words target j → r.val ≤ (circDist n startIndex.val j : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (∃ j, occursAt words target j) →
          ∀ j, occursAt words target j → r.val ≤ (circDist n startIndex.val j : Int)) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index j with 0 <= j < n such that the byte sequence words[j] equals the byte sequence target, then there exists an index j with 0 <= j < n such that words[j] equals target and r = min(|j - startIndex|, n - |j - startIndex|).
  Preconditions: Let n = len(words). We have 1 <= n <= 100; for every i with 0 <= i < n, len(words[i]) is between 1 and 100; every byte of every words[i] and of target is in the ASCII lowercase range 97..122; and startIndex is an integer satisfying 0 <= startIndex < n (it is passed as i64). -/
theorem spec_7
    (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)) :
    ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (∃ j, occursAt words target j) →
          ∃ j, occursAt words target j ∧ r.val = (circDist n startIndex.val j : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (startIndex : Std.I64)
    (n : Nat) (hn : n = words.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hword_len : ∀ (i : Nat) (h : i < n),
      1 ≤ (words.val[i]'(hn ▸ h)).val.length ∧ (words.val[i]'(hn ▸ h)).val.length ≤ 100)
    (hword_lower : ∀ w ∈ words.val, allBytesLower w.val)
    (htarget_lower : allBytesLower target.val)
    (hstart_lo : 0 ≤ startIndex.val) (hstart_hi : startIndex.val < (n : Int)), ∀ r : Std.I64,
      Aegis.ClosestTarget.closest_target words target startIndex = ok r →
        (∃ j, occursAt words target j) →
          ∃ j, occursAt words target j ∧ r.val = (circDist n startIndex.val j : Int)) := by
  sorry

end AegisSpec.ClosestTarget
