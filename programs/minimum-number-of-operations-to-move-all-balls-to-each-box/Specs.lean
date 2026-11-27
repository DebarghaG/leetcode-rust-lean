import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-number-of-operations-to-move-all-balls-to-each-box`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinOperations

namespace AegisSpec.MinOperations

def slen (boxes : Slice Std.U8) : ℕ := boxes.val.length

def inVal (boxes : Slice Std.U8) (i : ℕ) : ℕ :=
  match boxes.val[i]? with
  | some b => b.val
  | none => 0

abbrev isBall (boxes : Slice Std.U8) (i : ℕ) : Prop := inVal boxes i = 49

abbrev isBit (boxes : Slice Std.U8) (i : ℕ) : Prop := inVal boxes i = 48 ∨ inVal boxes i = 49

def outVal (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ :=
  match r.val[i]? with
  | some x => x.val
  | none => 0

def d (boxes : Slice Std.U8) (i j : ℕ) : ℤ :=
  if isBall boxes j then |(j : ℤ) - (i : ℤ)| else 0

def expected (boxes : Slice Std.U8) (i : ℕ) : ℤ :=
  Finset.sum (Finset.range (slen boxes)) (fun j => d boxes i j)

def ccost (boxes : Slice Std.U8) (j : ℕ) : ℤ :=
  if isBall boxes j then
    (j : ℤ) * ((j : ℤ) + 1) / 2
      + ((slen boxes : ℤ) - 1 - (j : ℤ)) * ((slen boxes : ℤ) - (j : ℤ)) / 2
  else 0

def cntLeft (boxes : Slice Std.U8) (i : ℕ) : ℕ :=
  ((Finset.range (i + 1)).filter (fun j => isBall boxes j)).card

def cntRight (boxes : Slice Std.U8) (i : ℕ) : ℕ :=
  ((Finset.Ico (i + 1) (slen boxes)).filter (fun j => isBall boxes j)).card

/-- The function returns a result r (it does not fail), and len(r) = n. For every i with 0 <= i < n, the I64 value r[i], viewed as a mathematical integer, equals sum_{j=0}^{n-1} d(i,j), where d(i,j) = |j-i| if boxes[j] = 49, and d(i,j) = 0 if boxes[j] = 48. Equivalently, r[i] is the minimum number of adjacent-box moves needed to move every ball present in boxes to box i, starting from the given initial configuration.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_1 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes → outVal r i = expected boxes i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes → outVal r i = expected boxes i) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r without failing.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_2 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∃ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∃ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r) := by
  sorry

/-- Whenever the function returns a result r, the length of r is len(boxes); that is, r has exactly one I64 value for each box.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_3 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r → r.val.length = slen boxes := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r → r.val.length = slen boxes) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, the I64 value r[i], viewed as a mathematical integer, is at least 0.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_4 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r → ∀ i, i < slen boxes → 0 ≤ outVal r i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∀ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r → ∀ i, i < slen boxes → 0 ≤ outVal r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, the I64 value r[i], viewed as a mathematical integer, is at most n*(n-1)/2.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_5 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r →
        ∀ i, i < slen boxes → outVal r i ≤ (slen boxes : ℤ) * ((slen boxes : ℤ) - 1) / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∀ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r →
        ∀ i, i < slen boxes → outVal r i ≤ (slen boxes : ℤ) * ((slen boxes : ℤ) - 1) / 2) := by
  sorry

/-- The function returns a result r with len(r) = n, and for every i with 0 <= i < n, r[i] = 0.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'), and in fact boxes[i] = 48 for every i. -/
theorem spec_6 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (hempty : ∀ i, i < slen boxes → inVal boxes i = 48) :
    ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes → outVal r i = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (hempty : ∀ i, i < slen boxes → inVal boxes i = 48), ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes → outVal r i = 0) := by
  sorry

/-- The function returns a result r with len(r) = 1 and r[0] = 0.
  Preconditions: len(boxes) = 1, and boxes[0] is either 48 ('0') or 49 ('1'). -/
theorem spec_7 (boxes : Slice Std.U8) (hn : slen boxes = 1) (h0 : isBit boxes 0) :
    ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = 1 ∧ outVal r 0 = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : slen boxes = 1) (h0 : isBit boxes 0), ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = 1 ∧ outVal r 0 = 0) := by
  sorry

/-- The function returns a result r with len(r) = n, and for every i with 0 <= i < n, the I64 value r[i], viewed as a mathematical integer, equals |i-k|.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'), and there exists k with 0 <= k < n such that boxes[k] = 49 and boxes[j] = 48 for every j with 0 <= j < n and j != k. -/
theorem spec_8 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (k : ℕ) (hk : k < slen boxes) (hkball : isBall boxes k)
    (honly : ∀ j, j < slen boxes → j ≠ k → inVal boxes j = 48) :
    ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes → outVal r i = |(i : ℤ) - (k : ℤ)| := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (k : ℕ) (hk : k < slen boxes) (hkball : isBall boxes k)
    (honly : ∀ j, j < slen boxes → j ≠ k → inVal boxes j = 48), ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes → outVal r i = |(i : ℤ) - (k : ℤ)|) := by
  sorry

/-- The function returns a result r with len(r) = n, and for every i with 0 <= i < n, the I64 value r[i], viewed as a mathematical integer, equals i*(i+1)/2 + (n-1-i)*(n-i)/2.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] = 49 ('1'). -/
theorem spec_9 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (hall : ∀ i, i < slen boxes → isBall boxes i) :
    ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes →
          outVal r i = (i : ℤ) * ((i : ℤ) + 1) / 2
            + ((slen boxes : ℤ) - 1 - (i : ℤ)) * ((slen boxes : ℤ) - (i : ℤ)) / 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (hall : ∀ i, i < slen boxes → isBall boxes i), ∃ r : alloc.vec.Vec Std.I64,
      min_operations boxes = ok r ∧ r.val.length = slen boxes ∧
        ∀ i, i < slen boxes →
          outVal r i = (i : ℤ) * ((i : ℤ) + 1) / 2
            + ((slen boxes : ℤ) - 1 - (i : ℤ)) * ((slen boxes : ℤ) - (i : ℤ)) / 2) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n-1, r[i+1]-r[i] equals P_i - S_i, where P_i is the number of indices j with 0 <= j <= i and boxes[j] = 49, and S_i is the number of indices j with i+1 <= j < n and boxes[j] = 49.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_10 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      ∀ i, i < slen boxes - 1 →
        outVal r (i + 1) - outVal r i = (cntLeft boxes i : ℤ) - (cntRight boxes i : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      ∀ i, i < slen boxes - 1 →
        outVal r (i + 1) - outVal r i = (cntLeft boxes i : ℤ) - (cntRight boxes i : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = r[n-1-i].
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'), and for every i with 0 <= i < n, boxes[i] = boxes[n-1-i]. -/
theorem spec_11 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (hsym : ∀ i, i < slen boxes → inVal boxes i = inVal boxes (slen boxes - 1 - i)) :
    ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      ∀ i, i < slen boxes → outVal r i = outVal r (slen boxes - 1 - i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i)
    (hsym : ∀ i, i < slen boxes → inVal boxes i = inVal boxes (slen boxes - 1 - i)), ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      ∀ i, i < slen boxes → outVal r i = outVal r (slen boxes - 1 - i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 0 if and only if every index j with 0 <= j < n and boxes[j] = 49 satisfies j = i.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_12 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      ∀ i, i < slen boxes →
        (outVal r i = 0 ↔ ∀ j, j < slen boxes → isBall boxes j → j = i) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      ∀ i, i < slen boxes →
        (outVal r i = 0 ↔ ∀ j, j < slen boxes → isBall boxes j → j = i)) := by
  sorry

/-- Whenever the function returns a result r, the sum_{i=0}^{n-1} r[i], viewed as a mathematical integer, equals sum_{j=0}^{n-1} c(j), where c(j) = j*(j+1)/2 + (n-1-j)*(n-j)/2 if boxes[j] = 49, and c(j) = 0 if boxes[j] = 48.
  Preconditions: Let n = len(boxes). We have 1 <= n <= 2000, and for every i with 0 <= i < n, boxes[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_13 (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i) :
    ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      Finset.sum (Finset.range (slen boxes)) (fun i => outVal r i)
        = Finset.sum (Finset.range (slen boxes)) (fun j => ccost boxes j) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (boxes : Slice Std.U8) (hn : 1 ≤ slen boxes)
    (hn2 : slen boxes ≤ 2000) (hbits : ∀ i, i < slen boxes → isBit boxes i), ∀ r : alloc.vec.Vec Std.I64, min_operations boxes = ok r →
      Finset.sum (Finset.range (slen boxes)) (fun i => outVal r i)
        = Finset.sum (Finset.range (slen boxes)) (fun j => ccost boxes j)) := by
  sorry

end AegisSpec.MinOperations
