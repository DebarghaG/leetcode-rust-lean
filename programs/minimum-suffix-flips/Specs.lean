import Aegis.MinFlips.Code.Funs

/-!
# Specifications of `Aegis.MinFlips.min_flips`

LeetCode problem `minimum-suffix-flips`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinFlips (min_flips)

  namespace AegisSpec.MinFlips

  def bitOfByte (b : U8) : ℕ := if b.val = 49 then 1 else 0

  def IsBinaryTarget (target : Slice U8) (maxLen : ℕ) : Prop :=
    1 ≤ target.val.length ∧ target.val.length ≤ maxLen ∧
      ∀ b ∈ target.val, b.val = 48 ∨ b.val = 49

  def flipByte (b : U8) : U8 := if b.val = 48 then 49#u8 else 48#u8

  def bits (t : List U8) : List ℕ := t.map bitOfByte

  def flipSuffix : ℕ → List ℕ → List ℕ
    | _, [] => []
    | 0, x :: xs => (1 - x) :: flipSuffix 0 xs
    | k + 1, x :: xs => x :: flipSuffix k xs

  def applyFlips (ops : List ℕ) (s : List ℕ) : List ℕ :=
    ops.foldl (fun s i => flipSuffix i s) s

  def zeros (n : ℕ) : List ℕ := List.replicate n 0

  def ValidOps (n : ℕ) (ops : List ℕ) : Prop := ∀ i ∈ ops, i < n

  def FlipsTo (t : List U8) (ops : List ℕ) : Prop :=
    applyFlips ops (zeros t.length) = bits t

  def FlipCosts (t : List U8) : Set ℕ :=
    { k | ∃ ops : List ℕ, ops.length = k ∧ ValidOps t.length ops ∧ FlipsTo t ops }

  noncomputable def minFlipCost (t : List U8) : ℕ := sInf (FlipCosts t)

  def bit (t : List U8) (p : ℕ) : ℕ :=
    match t[p]? with
    | some b => bitOfByte b
    | none => 0

  def prev (t : List U8) (p : ℕ) : ℕ := if p = 0 then 0 else bit t (p - 1)

  abbrev ChangeIdx (t : List U8) (p : ℕ) : Prop := bit t p ≠ prev t p

  def changeSet (t : List U8) : Set ℕ := { p | p < t.length ∧ ChangeIdx t p }

  def changeCount (t : List U8) : ℕ :=
    ((List.range t.length).filter (fun p => decide (ChangeIdx t p))).length

  abbrev OnesBlockStart (t : List U8) (p : ℕ) : Prop :=
    p < t.length ∧ bit t p = 1 ∧ prev t p = 0

  def numOneBlocks (t : List U8) : ℕ :=
    ((List.range t.length).filter (fun p => decide (OnesBlockStart t p))).length

  def lastBit (t : List U8) : ℕ := bit t (t.length - 1)

  def oddUsedCount (t : List U8) (ops : List ℕ) : ℕ :=
    ((List.range t.length).filter (fun p => decide (Odd (ops.count p)))).length

  /-- Whenever the function returns a result r, interpreting the I64 result as an integer, r is the minimum k >= 0 for which there exist indices i_0, ..., i_{k-1} with 0 <= i_t < len(target) such that the following process yields target: start with a string of len(target) ASCII '0' bytes; for t = 0, ..., k-1, flip every byte in positions i_t through len(target)-1 (change '0' to '1' and '1' to '0'); after all k operations the byte at every position p with 0 <= p < len(target) equals target[p]. The minimum is over all such k and all such sequences; for k = 0 no operation is performed.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_1 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      r.val = (minFlipCost target.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), r.val = (minFlipCost target.val : ℤ)) := by
    sorry

  /-- For every target satisfying the preconditions, the function returns a result r (that is, execution does not fail, panic, overflow, or access memory out of bounds).
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_2 (target : Slice U8) (htarget : IsBinaryTarget target 100000) :
      ∃ r : I64, min_flips target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000), ∃ r : I64, min_flips target = ok r) := by
    sorry

  /-- Whenever the function returns r, r equals the number of indices j with 0 <= j < len(target) such that bit(j) differs from prev(j), where bit(j) = 1 if target[j] is ASCII '1' (49) and bit(j) = 0 if target[j] is ASCII '0' (48), prev(0) = 0, and prev(j) = bit(j-1) for j > 0.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_3 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      r.val = (changeCount target.val : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), r.val = (changeCount target.val : ℤ)) := by
    sorry

  /-- Whenever the function returns r, 0 <= r <= len(target).
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_4 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      0 ≤ r.val ∧ r.val ≤ (target.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), 0 ≤ r.val ∧ r.val ≤ (target.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns r, r = 0 if and only if every byte of target is ASCII '0' (48); that is, target[p] = 48 for all p with 0 <= p < len(target).
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_5 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      (r.val = 0 ↔ ∀ (p : ℕ) (h : p < target.val.length), (target.val.get ⟨p, h⟩).val = 48) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), (r.val = 0 ↔ ∀ (p : ℕ) (h : p < target.val.length), (target.val.get ⟨p, h⟩).val = 48)) := by
    sorry

  /-- Whenever the function returns r, the integer r is odd if and only if target[len(target)-1] is ASCII '1' (49), and r is even if and only if target[len(target)-1] is ASCII '0' (48).
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_6 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      (Odd r.val ↔ lastBit target.val = 1) ∧ (Even r.val ↔ lastBit target.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), (Odd r.val ↔ lastBit target.val = 1) ∧ (Even r.val ↔ lastBit target.val = 0)) := by
    sorry

  /-- Whenever the function returns r, let R be the number of maximal nonempty contiguous blocks of indices p for which target[p] is ASCII '1' (a block is a contiguous interval of indices all equal to '1', and it is maximal if it cannot be extended left or right while staying inside target and remaining all '1'). Let E = 1 if target[len(target)-1] is ASCII '1' (49), and E = 0 otherwise. Then r = 2*R - E.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_7 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      r.val = 2 * (numOneBlocks target.val : ℤ) - (lastBit target.val : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), r.val = 2 * (numOneBlocks target.val : ℤ) - (lastBit target.val : ℤ)) := by
    sorry

  /-- Whenever the function returns r, for every k >= 0 and every sequence i_0, ..., i_{k-1} of indices with 0 <= i_t < len(target), if starting from the all-zero string of length len(target) and applying the suffix flips [i_t, len(target)-1] for t = 0, ..., k-1 produces target, then k >= r.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_8 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      ∀ ops : List ℕ, ValidOps target.val.length ops → FlipsTo target.val ops →
        r.val ≤ (ops.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), ∀ ops : List ℕ, ValidOps target.val.length ops → FlipsTo target.val ops →
          r.val ≤ (ops.length : ℤ)) := by
    sorry

  /-- Whenever the function returns r, there exists a sequence i_0, ..., i_{r-1} of indices with 0 <= i_t < len(target) such that starting from the all-zero string of length len(target) and applying the suffix flips [i_t, len(target)-1] for t = 0, ..., r-1 produces target.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_9 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      ∃ ops : List ℕ, ValidOps target.val.length ops ∧ FlipsTo target.val ops ∧
        (ops.length : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), ∃ ops : List ℕ, ValidOps target.val.length ops ∧ FlipsTo target.val ops ∧
          (ops.length : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns r, in every sequence of suffix-flip operations of any length that transforms the all-zero string of length len(target) into target, for each index j with 0 <= j < len(target), the number of times the operation starting at j is used is odd exactly when bit(j) differs from prev(j), where bit(j) = 1 if target[j] is ASCII '1' (49) and bit(j) = 0 if target[j] is ASCII '0' (48), prev(0) = 0, and prev(j) = bit(j-1) for j > 0. Consequently, in every such successful sequence the number of indices used an odd number of times is r.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_10 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      ∀ ops : List ℕ, ValidOps target.val.length ops → FlipsTo target.val ops →
        (∀ p, p < target.val.length → (Odd (ops.count p) ↔ ChangeIdx target.val p)) ∧
          (oddUsedCount target.val ops : ℤ) = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), ∀ ops : List ℕ, ValidOps target.val.length ops → FlipsTo target.val ops →
          (∀ p, p < target.val.length → (Odd (ops.count p) ↔ ChangeIdx target.val p)) ∧
            (oddUsedCount target.val ops : ℤ) = r.val) := by
    sorry

  /-- Whenever the call min_flips(target) returns r and the call min_flips(target') returns r', the integers r and r' are equal.
    Preconditions: target is a binary string: 1 <= len(target) <= 99999, and for every i with 0 <= i < len(target), target[i] is ASCII '0' (48) or ASCII '1' (49). Let target' be the binary string of length len(target)+1 defined by target'[0] = ASCII '0' (48) and target'[p+1] = target[p] for every p with 0 <= p < len(target). -/
  theorem spec_11 (target target' : Slice U8) (htarget : IsBinaryTarget target 99999)
      (htarget' : target'.val = 48#u8 :: target.val) (r r' : I64)
      (hr : min_flips target = ok r) (hr' : min_flips target' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (target target' : Slice U8) (htarget : IsBinaryTarget target 99999)
        (htarget' : target'.val = 48#u8 :: target.val) (r r' : I64)
        (hr : min_flips target = ok r) (hr' : min_flips target' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the call min_flips(target) returns r and the call min_flips(target') returns r', the integers r and r' satisfy r' = r + 1.
    Preconditions: target is a binary string: 1 <= len(target) <= 99999, and for every i with 0 <= i < len(target), target[i] is ASCII '0' (48) or ASCII '1' (49). Let target' be the binary string of length len(target)+1 defined by target'[p] = target[p] for 0 <= p < len(target), and target'[len(target)] is ASCII '1' (49) if target[len(target)-1] is ASCII '0' (48), and is ASCII '0' (48) if target[len(target)-1] is ASCII '1' (49). -/
  theorem spec_12 (target target' : Slice U8) (htarget : IsBinaryTarget target 99999)
      (htarget' : target'.val = target.val ++ [flipByte (target.val.getLastD 0#u8)])
      (r r' : I64) (hr : min_flips target = ok r) (hr' : min_flips target' = ok r') :
      r'.val = r.val + 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (target target' : Slice U8) (htarget : IsBinaryTarget target 99999)
        (htarget' : target'.val = target.val ++ [flipByte (target.val.getLastD 0#u8)])
        (r r' : I64) (hr : min_flips target = ok r) (hr' : min_flips target' = ok r'), r'.val = r.val + 1) := by
    sorry

  /-- Whenever the function returns r, define bit(p) = 1 if target[p] is ASCII '1' (49) and bit(p) = 0 otherwise, with prev(0) = 0 and prev(p) = bit(p-1) for p > 0. Let J = { j | 0 <= j < len(target) and bit(j) differs from prev(j) }. Then |J| = r, and for every ordering j_0, ..., j_{r-1} of J, starting from the all-zero string of length len(target) and applying the suffix flips [j_t, len(target)-1] for t = 0, ..., r-1 in that order produces target.
    Preconditions: target is a binary string: 1 <= len(target) <= 100000, and for every i with 0 <= i < len(target), target[i] is the ASCII byte for '0' (48) or for '1' (49). -/
  theorem spec_13 (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
      (hr : min_flips target = ok r) :
      (changeCount target.val : ℤ) = r.val ∧
        ∀ ops : List ℕ, ops.Nodup → (∀ p, p ∈ ops ↔ p ∈ changeSet target.val) →
          FlipsTo target.val ops := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (target : Slice U8) (htarget : IsBinaryTarget target 100000) (r : I64)
        (hr : min_flips target = ok r), (changeCount target.val : ℤ) = r.val ∧
          ∀ ops : List ℕ, ops.Nodup → (∀ p, p ∈ ops ↔ p ∈ changeSet target.val) →
            FlipsTo target.val ops) := by
    sorry

  end AegisSpec.MinFlips
