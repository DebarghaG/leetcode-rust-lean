import Aegis.LongestString.Code.Funs

/-!
# Specifications of `Aegis.LongestString.longest_string`

LeetCode problem `construct-the-longest-new-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestString

inductive Block where
  | AA
  | BB
  | AB
  deriving DecidableEq, Repr

namespace Block

def toList : Block → List Char
  | Block.AA => ['A', 'A']
  | Block.BB => ['B', 'B']
  | Block.AB => ['A', 'B']

end Block

def countBlock (b : Block) (bs : List Block) : Nat :=
  (bs.filter fun b' => decide (b' = b)).length

def concatBlocks (bs : List Block) : List Char :=
  bs.flatMap Block.toList

def IsOrdering (a b c : Int) (bs : List Block) : Prop :=
  (countBlock Block.AA bs : Int) = a ∧
    (countBlock Block.BB bs : Int) = b ∧
      (countBlock Block.AB bs : Int) = c

def IsSubstring (p s : List Char) : Prop :=
  ∃ l r : List Char, s = l ++ p ++ r

def AvoidsTriple (s : List Char) : Prop :=
  ¬ IsSubstring ['A', 'A', 'A'] s ∧ ¬ IsSubstring ['B', 'B', 'B'] s

def OrdersWithoutTriple (bs : List Block) : Prop :=
  AvoidsTriple (concatBlocks bs)

/-- Let m = min(x, y) and M = max(x, y). The function returns a result r, and r = 2 * (z + m + min(M, m + 1)). Equivalently, r is the maximum possible length, in characters, of a string obtained by choosing some of the x copies of "AA", y copies of "BB", and z copies of "AB" and concatenating the chosen strings in some order so that the resulting string contains neither "AAA" nor "BBB" as a contiguous substring.
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_1 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestString.longest_string x y z = ok r ∧
        r.val = 2 * (z.val + min x.val y.val +
          min (max x.val y.val) (min x.val y.val + 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∃ r : Std.I64,
      Aegis.LongestString.longest_string x y z = ok r ∧
        r.val = 2 * (z.val + min x.val y.val +
          min (max x.val y.val) (min x.val y.val + 1))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_2 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∃ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∃ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= 2 * (x + y + z).
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_3 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      r.val ≤ 2 * (x.val + y.val + z.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      r.val ≤ 2 * (x.val + y.val + z.val)) := by
  sorry

/-- Whenever the function returns a result r, r >= 2 * (z + 2 * min(x, y)).
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_4 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      2 * (z.val + 2 * min x.val y.val) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      2 * (z.val + 2 * min x.val y.val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 2 * (z + 2 * min(x, y) + 1).
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_5 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      r.val ≤ 2 * (z.val + 2 * min x.val y.val + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      r.val ≤ 2 * (z.val + 2 * min x.val y.val + 1)) := by
  sorry

/-- Whenever the function returns a result r, r = 2 * (x + y + z) if and only if |x - y| <= 1.
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_6 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      (r.val = 2 * (x.val + y.val + z.val) ↔ (x.val - y.val).natAbs ≤ 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      (r.val = 2 * (x.val + y.val + z.val) ↔ (x.val - y.val).natAbs ≤ 1)) := by
  sorry

/-- Whenever the function returns a result r, for every integers a, b, c with 0 <= a <= x, 0 <= b <= y, and 0 <= c <= z, and for every ordering of a copies of "AA", b copies of "BB", and c copies of "AB", if the concatenation of that ordering contains neither "AAA" nor "BBB" as a contiguous substring, then 2 * (a + b + c) <= r.
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_7 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      ∀ (a b c : Int) (bs : List Block),
        0 ≤ a → a ≤ x.val → 0 ≤ b → b ≤ y.val → 0 ≤ c → c ≤ z.val →
          IsOrdering a b c bs → OrdersWithoutTriple bs → 2 * (a + b + c) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      ∀ (a b c : Int) (bs : List Block),
        0 ≤ a → a ≤ x.val → 0 ≤ b → b ≤ y.val → 0 ≤ c → c ≤ z.val →
          IsOrdering a b c bs → OrdersWithoutTriple bs → 2 * (a + b + c) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist integers a, b and an ordering of a copies of "AA", b copies of "BB", and all z copies of "AB" such that 0 <= a <= x, 0 <= b <= y, the concatenation contains neither "AAA" nor "BBB" as a contiguous substring, and 2 * (a + b + z) = r.
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_8 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      ∃ (a b : Int) (bs : List Block),
        0 ≤ a ∧ a ≤ x.val ∧ 0 ≤ b ∧ b ≤ y.val ∧
          IsOrdering a b z.val bs ∧ OrdersWithoutTriple bs ∧
            2 * (a + b + z.val) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      ∃ (a b : Int) (bs : List Block),
        0 ≤ a ∧ a ≤ x.val ∧ 0 ≤ b ∧ b ≤ y.val ∧
          IsOrdering a b z.val bs ∧ OrdersWithoutTriple bs ∧
            2 * (a + b + z.val) = r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist integers a, b, c and an ordering of a copies of "AA", b copies of "BB", and c copies of "AB" such that 0 <= a <= x, 0 <= b <= y, 0 <= c <= z, |a - b| <= 1, the concatenation contains neither "AAA" nor "BBB" as a contiguous substring, and 2 * (a + b + c) = r.
  Preconditions: x, y, and z are integers satisfying 1 <= x <= 50, 1 <= y <= 50, and 1 <= z <= 50. -/
theorem spec_9 (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50) :
    ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      ∃ (a b c : Int) (bs : List Block),
        0 ≤ a ∧ a ≤ x.val ∧ 0 ≤ b ∧ b ≤ y.val ∧ 0 ≤ c ∧ c ≤ z.val ∧
          (a - b).natAbs ≤ 1 ∧ IsOrdering a b c bs ∧ OrdersWithoutTriple bs ∧
            2 * (a + b + c) = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x y z : Std.I64)
    (hx : 1 ≤ x.val ∧ x.val ≤ 50)
    (hy : 1 ≤ y.val ∧ y.val ≤ 50)
    (hz : 1 ≤ z.val ∧ z.val ≤ 50), ∀ r : Std.I64, Aegis.LongestString.longest_string x y z = ok r →
      ∃ (a b c : Int) (bs : List Block),
        0 ≤ a ∧ a ≤ x.val ∧ 0 ≤ b ∧ b ≤ y.val ∧ 0 ≤ c ∧ c ≤ z.val ∧
          (a - b).natAbs ≤ 1 ∧ IsOrdering a b c bs ∧ OrdersWithoutTriple bs ∧
            2 * (a + b + c) = r.val) := by
  sorry

end AegisSpec.LongestString
