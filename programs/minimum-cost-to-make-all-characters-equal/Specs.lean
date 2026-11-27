import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-to-make-all-characters-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumCost

namespace AegisSpec.MinimumCost

def codeAt (s : Slice Std.U8) (i : Nat) : Nat := (s.val.getD i 0#u8).val

def isBits (s : Slice Std.U8) : Prop :=
  ∀ i, i < s.val.length → codeAt s i = 48 ∨ codeAt s i = 49

def allSame (s : Slice Std.U8) : Prop :=
  ∀ i j, i < s.val.length → j < s.val.length → codeAt s i = codeAt s j

def alternating (s : Slice Std.U8) : Prop :=
  ∀ i, i + 1 < s.val.length → codeAt s i ≠ codeAt s (i + 1)

def changes (s : Slice Std.U8) : Finset Nat :=
  (Finset.range (s.val.length - 1)).filter (fun i => codeAt s i ≠ codeAt s (i + 1))

def costSum (s : Slice Std.U8) : Nat :=
  ∑ i ∈ changes s, min (i + 1) (s.val.length - i - 1)

def maxCost (n : Nat) : Nat := (n / 2) * ((n + 1) / 2)

def codes (s : Slice Std.U8) : List Nat := s.val.map (fun c => c.val)

def flipCode (c : Nat) : Nat := if c = 48 then 49 else if c = 49 then 48 else c

def allEqualCodes (l : List Nat) : Prop :=
  ∀ i j, i < l.length → j < l.length → l.getD i 0 = l.getD j 0

inductive Op (n : Nat) where

  | prefix (i : Nat) (hi : i < n)

  | suffix (i : Nat) (hi : i < n)

namespace Op
variable {n : Nat}

def cost : Op n → Nat
  | .prefix i _ => i + 1
  | .suffix i _ => n - i

def apply (l : List Nat) : Op n → List Nat
  | .prefix i _ => (l.take (i + 1)).map flipCode ++ l.drop (i + 1)
  | .suffix i _ => l.take i ++ (l.drop i).map flipCode

end Op

def opsCost {n : Nat} (ops : List (Op n)) : Nat := (ops.map Op.cost).sum

def runOps {n : Nat} (l : List Nat) : List (Op n) → List Nat
  | [] => l
  | o :: os => runOps (Op.apply l o) os

/-- The function returns a result r and r equals the sum, over all i with 0 <= i < n-1 and s[i] != s[i+1], of min(i+1, n-i-1). The sum over an empty set of indices is 0.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1' (that is, s[i] = 48 or s[i] = 49). -/
theorem spec_1 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧ r.val = (costSum s : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧ r.val = (costSum s : Int)) := by
  sorry

/-- Let k be the number of indices i with 0 <= i < n-1 and s[i] != s[i+1]. The function returns a result r and r >= k.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_2 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧ ((changes s).card : Int) ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧ ((changes s).card : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= floor(n/2) * ceil(n/2). Equivalently, for integer n >= 0, r <= (n / 2) * ((n + 1) / 2) using integer division.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_3 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧ r.val ≤ (maxCost s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧ r.val ≤ (maxCost s.val.length : Int)) := by
  sorry

/-- The function returns a result r and r = 0 if and only if all characters of s are equal, i.e., for every i and j with 0 <= i < n and 0 <= j < n, s[i] = s[j].
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_4 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧ (r.val = 0 ↔ allSame s) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧ (r.val = 0 ↔ allSame s)) := by
  sorry

/-- The function returns results on both inputs s and t, and the result for s equals the result for t.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. Let t be any slice of length n whose entries are ASCII '0' or '1' and such that t[i] = s[n-1-i] for every 0 <= i < n. -/
theorem spec_5 (s t : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s)
    (htlen : t.val.length = s.val.length) (htbits : isBits t)
    (hrev : ∀ i, i < s.val.length → codeAt t i = codeAt s (s.val.length - 1 - i)) :
    ∃ r r' : Std.I64,
      minimum_cost s = ok r ∧ minimum_cost t = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s)
    (htlen : t.val.length = s.val.length) (htbits : isBits t)
    (hrev : ∀ i, i < s.val.length → codeAt t i = codeAt s (s.val.length - 1 - i)), ∃ r r' : Std.I64,
      minimum_cost s = ok r ∧ minimum_cost t = ok r' ∧ r.val = r'.val) := by
  sorry

/-- The function returns a result r and there exists a finite sequence of allowed operations whose total cost is exactly r and which transforms s into a string all of whose characters are equal. An allowed operation is either: choose i with 0 <= i < n and invert s[0..i] at cost i+1, or choose i with 0 <= i < n and invert s[i..n-1] at cost n-i.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_6 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧
      ∃ ops : List (Op s.val.length),
        (opsCost ops : Int) = r.val ∧ allEqualCodes (runOps (codes s) ops) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧
      ∃ ops : List (Op s.val.length),
        (opsCost ops : Int) = r.val ∧ allEqualCodes (runOps (codes s) ops)) := by
  sorry

/-- The function returns a result r and for every finite sequence of allowed prefix/suffix inversion operations with total cost C that transforms s into a string all of whose characters are equal, r <= C.
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_7 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧
      ∀ ops : List (Op s.val.length),
        allEqualCodes (runOps (codes s) ops) → r.val ≤ (opsCost ops : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧
      ∀ ops : List (Op s.val.length),
        allEqualCodes (runOps (codes s) ops) → r.val ≤ (opsCost ops : Int)) := by
  sorry

/-- The function returns a result r and r = floor(n/2) * ceil(n/2) if and only if s is alternating, i.e., for every i with 0 <= i < n-1, s[i] != s[i+1].
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_8 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64,
      minimum_cost s = ok r ∧ (r.val = (maxCost s.val.length : Int) ↔ alternating s) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64,
      minimum_cost s = ok r ∧ (r.val = (maxCost s.val.length : Int) ↔ alternating s)) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < n-1 and s[i] != s[i+1], r >= min(i+1, n-i-1).
  Preconditions: Let n = len(s). 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is the ASCII code of '0' or '1'. -/
theorem spec_9 (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s) :
    ∃ r : Std.I64, minimum_cost s = ok r ∧
      ∀ i, i + 1 < s.val.length → codeAt s i ≠ codeAt s (i + 1) →
        ((min (i + 1) (s.val.length - i - 1) : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hpos : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100000) (hbits : isBits s), ∃ r : Std.I64, minimum_cost s = ok r ∧
      ∀ i, i + 1 < s.val.length → codeAt s i ≠ codeAt s (i + 1) →
        ((min (i + 1) (s.val.length - i - 1) : Nat) : Int) ≤ r.val) := by
  sorry

end AegisSpec.MinimumCost
