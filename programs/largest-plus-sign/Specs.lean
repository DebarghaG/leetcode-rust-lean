import Aegis.OrderOfLargestPlusSign.Code.Funs

/-!
# Specifications of `Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign`

LeetCode problem `largest-plus-sign`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.OrderOfLargestPlusSign

def mineCoords (mines : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
  ((mines.val[i]?).map (fun v => v.val.map (fun x => x.val))).getD []

def allCoords (mines : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  mines.val.map (fun v => v.val.map (fun x => x.val))

def NValid (n : Std.I64) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 500

def MinesValid (n : ℤ) (mines : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  mines.val.length ≤ 5000 ∧
    ∀ i : ℕ, i < mines.val.length →
      ∃ a b : ℤ, mineCoords mines i = [a, b] ∧ 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n

def MinesDistinct (mines : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (allCoords mines).Nodup

def IsMined (mines : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
  ∃ i : ℕ, i < mines.val.length ∧ mineCoords mines i = [a, b]

def IsOpen (n : ℤ) (mines : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
  0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧ ¬ IsMined mines a b

def Plus (n : ℤ) (mines : Slice (alloc.vec.Vec Std.I64)) (k a b : ℤ) : Prop :=
  1 ≤ k ∧ IsOpen n mines a b ∧
    ∀ d : ℤ, 0 ≤ d → d < k →
      IsOpen n mines (a - d) b ∧ IsOpen n mines (a + d) b ∧
        IsOpen n mines a (b - d) ∧ IsOpen n mines a (b + d)

/-- Call a cell (a,b) open if 0 <= a < n, 0 <= b < n, and there is no i with 0 <= i < len(mines) such that mines[i][0] = a and mines[i][1] = b. Call plus(k,a,b) true if k >= 1, (a,b) is open, and for every d with 0 <= d < k the four cells (a-d,b), (a+d,b), (a,b-d), (a,b+d) are all open. The function returns a result r, and exactly one of the following holds: (1) r = 0 and for every k >= 1 and all integers a,b, plus(k,a,b) is false; or (2) r >= 1, there exist integers a,b with plus(r,a,b), and for every k > r and all integers a,b, plus(k,a,b) is false. Equivalently, r is the largest order of an axis-aligned plus sign of 1's in the n x n grid, or 0 if no such plus exists.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. The provided examples include mines = [], so the empty list is admitted here; if the original problem's 1 <= mines.length constraint is imposed, restrict to len(mines) >= 1. -/
theorem spec_1 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        ((r.val = 0 ∧ ∀ (k : ℤ) (a b : ℤ), ¬ Plus n.val mines k a b) ∨
          (1 ≤ r.val ∧ (∃ a b : ℤ, Plus n.val mines r.val a b) ∧
            ∀ (k : ℤ) (a b : ℤ), r.val < k → ¬ Plus n.val mines k a b)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        ((r.val = 0 ∧ ∀ (k : ℤ) (a b : ℤ), ¬ Plus n.val mines k a b) ∨
          (1 ≤ r.val ∧ (∃ a b : ℤ, Plus n.val mines r.val a b) ∧
            ∀ (k : ℤ) (a b : ℤ), r.val < k → ¬ Plus n.val mines k a b))) := by
  sorry

/-- The function returns a result r and 0 <= r. Moreover, if r > 0 then 2*r - 1 <= n; equivalently r <= floor((n+1)/2).
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_2 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        0 ≤ r.val ∧ (0 < r.val → 2 * r.val - 1 ≤ n.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        0 ≤ r.val ∧ (0 < r.val → 2 * r.val - 1 ≤ n.val)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if for every row a and column b with 0 <= a < n and 0 <= b < n there exists i with 0 <= i < len(mines) such that mines[i][0] = a and mines[i][1] = b. In other words, r = 0 exactly when every cell of the n x n grid is mined, so no open cell exists.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_3 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        (r.val = 0 ↔
          ∀ a b : ℤ, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val → IsMined mines a b) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        (r.val = 0 ↔
          ∀ a b : ℤ, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val → IsMined mines a b)) := by
  sorry

/-- Call a cell (a,b) open if 0 <= a < n, 0 <= b < n, and there is no i with 0 <= i < len(mines) such that mines[i][0] = a and mines[i][1] = b. Call plus(k,a,b) true if k >= 1, (a,b) is open, and for every d with 0 <= d < k the four cells (a-d,b), (a+d,b), (a,b-d), (a,b+d) are all open. Whenever the function returns a result r with r > 0, there exist integers a,b such that plus(r,a,b) holds.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_4 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        0 < r.val → ∃ a b : ℤ, Plus n.val mines r.val a b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        0 < r.val → ∃ a b : ℤ, Plus n.val mines r.val a b) := by
  sorry

/-- Call a cell (a,b) open if 0 <= a < n, 0 <= b < n, and there is no i with 0 <= i < len(mines) such that mines[i][0] = a and mines[i][1] = b. Call plus(k,a,b) true if k >= 1, (a,b) is open, and for every d with 0 <= d < k the four cells (a-d,b), (a+d,b), (a,b-d), (a,b+d) are all open. Whenever the function returns a result r, for every k > r and all integers a,b, plus(k,a,b) is false.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_5 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        ∀ (k : ℤ) (a b : ℤ), r.val < k → ¬ Plus n.val mines k a b := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        ∀ (k : ℤ) (a b : ℤ), r.val < k → ¬ Plus n.val mines k a b) := by
  sorry

/-- Call a cell (a,b) open if 0 <= a < n, 0 <= b < n, and there is no i with 0 <= i < len(mines) such that mines[i][0] = a and mines[i][1] = b. Call plus(k,a,b) true if k >= 1, (a,b) is open, and for every d with 0 <= d < k the four cells (a-d,b), (a+d,b), (a,b-d), (a,b+d) are all open. Whenever the function returns a result r, for every k >= 1 and all integers a,b, if plus(k,a,b) holds then k <= r.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_6 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        ∀ (k : ℤ) (a b : ℤ), 1 ≤ k → Plus n.val mines k a b → k ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        ∀ (k : ℤ) (a b : ℤ), 1 ≤ k → Plus n.val mines k a b → k ≤ r.val) := by
  sorry

/-- The function returns a result r and r = ceil(n/2); equivalently r = floor((n+1)/2).
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with len(mines) = 0; all other standard validity conditions hold vacuously. Lists and indices are 0-based. -/
theorem spec_7 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hempty : mines.val = []) :
    ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        r.val = (n.val + 1) / 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hempty : mines.val = []), ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        r.val = (n.val + 1) / 2) := by
  sorry

/-- The function returns a result r, and r = 1 if there is no i with 0 <= i < len(mines) such that mines[i][0] = 0 and mines[i][1] = 0; otherwise r = 0.
  Preconditions: n is an integer with n = 1; mines is a list of length len(mines) with 0 <= len(mines) <= 1; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] = 0 and mines[i][1] = 0; all pairs are distinct. Lists and indices are 0-based. -/
theorem spec_8 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : n.val = 1) (hlen : mines.val.length ≤ 1)
    (hmines : ∀ i : ℕ, i < mines.val.length → mineCoords mines i = [0, 0])
    (hd : MinesDistinct mines) :
    ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        ((¬ IsMined mines 0 0) → r.val = 1) ∧ (IsMined mines 0 0 → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : n.val = 1) (hlen : mines.val.length ≤ 1)
    (hmines : ∀ i : ℕ, i < mines.val.length → mineCoords mines i = [0, 0])
    (hd : MinesDistinct mines), ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r ∧
        ((¬ IsMined mines 0 0) → r.val = 1) ∧ (IsMined mines 0 0 → r.val = 0)) := by
  sorry

/-- Call a cell (a,b) open if 0 <= a < n, 0 <= b < n, and there is no i with 0 <= i < len(mines) such that mines[i][0] = a and mines[i][1] = b. Call plus(k,a,b) true if k >= 1, (a,b) is open, and for every d with 0 <= d < k the four cells (a-d,b), (a+d,b), (a,b-d), (a,b+d) are all open. Whenever the function returns a result r, r = 1 if and only if (there exist integers a,b such that (a,b) is open) and (for all integers c,d, plus(2,c,d) is false).
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_9 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        (r.val = 1 ↔
          (∃ a b : ℤ, IsOpen n.val mines a b) ∧ ∀ (c d : ℤ), ¬ Plus n.val mines 2 c d) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∀ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        (r.val = 1 ↔
          (∃ a b : ℤ, IsOpen n.val mines a b) ∧ ∀ (c d : ℤ), ¬ Plus n.val mines 2 c d)) := by
  sorry

/-- Whenever the function returns a result r on input (n, mines) and a result r2 on input (n, mines2), we have r = r2.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. mines2 is any list obtained by permuting the entries of mines (so len(mines2) = len(mines) and mines2 has the same multiset of pairs). -/
theorem spec_10 (n : Std.I64) (mines mines2 : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines)
    (hperm : List.Perm mines.val mines2.val) :
    ∀ r r2 : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines2 = ok r2 →
          r.val = r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (mines mines2 : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines)
    (hperm : List.Perm mines.val mines2.val), ∀ r r2 : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines2 = ok r2 →
          r.val = r2.val) := by
  sorry

/-- Whenever the function returns a result r on input (n, mines) and a result r2 on input (n, mines2), we have r2 <= r.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. mines2 is any list satisfying the same validity conditions for the same n, with len(mines2) <= 5000, such that every pair occurring in mines also occurs in mines2 (so mines2 may add more mined cells). -/
theorem spec_11 (n : Std.I64) (mines mines2 : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines)
    (hm2 : MinesValid n.val mines2) (hd2 : MinesDistinct mines2)
    (hsub : ∀ a b : ℤ, IsMined mines a b → IsMined mines2 a b) :
    ∀ r r2 : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines2 = ok r2 →
          r2.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (mines mines2 : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines)
    (hm2 : MinesValid n.val mines2) (hd2 : MinesDistinct mines2)
    (hsub : ∀ a b : ℤ, IsMined mines a b → IsMined mines2 a b), ∀ r r2 : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r →
        Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines2 = ok r2 →
          r2.val ≤ r.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an array out of bounds.
  Preconditions: n is an integer with 1 <= n <= 500; mines is a list of length len(mines) with 0 <= len(mines) <= 5000; for every i with 0 <= i < len(mines), mines[i] is a list of length 2, mines[i][0] and mines[i][1] are integers with 0 <= mines[i][0] < n and 0 <= mines[i][1] < n, and all pairs (mines[i][0], mines[i][1]) are distinct. Lists and indices are 0-based. -/
theorem spec_12 (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines) :
    ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (mines : Slice (alloc.vec.Vec Std.I64))
    (hn : NValid n) (hm : MinesValid n.val mines) (hd : MinesDistinct mines), ∃ r : Std.I64,
      Aegis.OrderOfLargestPlusSign.order_of_largest_plus_sign n mines = ok r) := by
  sorry

end AegisSpec.OrderOfLargestPlusSign
