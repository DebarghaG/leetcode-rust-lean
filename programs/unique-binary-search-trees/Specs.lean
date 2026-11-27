import Aegis.NumTrees.Code.Funs

/-!
# Specifications of `Aegis.NumTrees.num_trees`

LeetCode problem `unique-binary-search-trees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumTrees

def shapeTable : Nat → List Nat
  | 0 => []
  | k + 1 =>
    let bs := shapeTable k
    bs ++ [if k = 0 then 1 else ((bs.zip bs.reverse).map fun p => p.1 * p.2).sum]

def bstCount (n : Nat) : Nat := ((shapeTable (n + 1)).reverse).headD 0

def catalan (n : Nat) : Nat := ((shapeTable (n + 1)).reverse).headD 0

def binom (a b : Nat) : Nat := a.factorial / (b.factorial * (a - b).factorial)

def allStepLists : Nat → List (List Int)
  | 0 => [[]]
  | k + 1 => (allStepLists k).flatMap fun s => [1 :: s, (-1) :: s]

def IsDyckPath (n : Nat) (s : List Int) : Prop :=
  s.length = 2 * n ∧
    s.count 1 = n ∧
      s.count (-1) = n ∧
        (∀ k, k ≤ s.length → 0 ≤ (s.take k).sum) ∧ s.sum = 0

instance (n : Nat) (s : List Int) : Decidable (IsDyckPath n s) := by
  unfold IsDyckPath
  infer_instance

def dyckPathCount (n : Nat) : Nat :=
  ((allStepLists (2 * n)).filter fun s => decide (IsDyckPath n s)).length

/-- The function returns a result r and does not fail, with r = C_n, where C_n is the number of structurally distinct binary search trees with exactly n nodes whose node values are the distinct integers 1,2,...,n. Two such BSTs are counted as structurally the same exactly when they have the same shape; the node values are then forced by the BST ordering. Equivalently, C_n is the n-th Catalan number.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val = (bstCount n.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val = (bstCount n.val.toNat : Int)) := by
  sorry

/-- For every such n, the function returns a result and does not fail: no arithmetic overflow, no out-of-bounds access, no panic, and no other runtime failure occurs.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r) := by
  sorry

/-- The returned value r satisfies r = binom(2n, n) / (n+1), where binom(a,b) denotes the binomial coefficient a! / (b! * (a-b)!) for 0 <= b <= a. The division is exact in the integers.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧
      r.val = ((binom (2 * n.val.toNat) n.val.toNat / (n.val.toNat + 1) : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧
      r.val = ((binom (2 * n.val.toNat) n.val.toNat / (n.val.toNat + 1) : Nat) : Int)) := by
  sorry

/-- Let C_0 = 1 and, for every k >= 1, let C_k = sum_{i=0}^{k-1} C_i * C_{k-1-i}. The returned value r satisfies r = C_n.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val = (catalan n.val.toNat : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val = (catalan n.val.toNat : Int)) := by
  sorry

/-- The returned value r is positive: r >= 1.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The returned value r is at most 1767263190.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val ≤ 1767263190 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val ≤ 1767263190) := by
  sorry

/-- The function returns results r_m and r_n, and r_m < r_n. Thus the answer is strictly increasing over the allowed input range 1..19.
  Preconditions: m and n are integers with 1 <= m < n <= 19. Let r_m be the result returned by the function on input m, and let r_n be the result returned by the function on input n. -/
theorem spec_7 (m n : Std.I64) (hm : 1 ≤ m.val ∧ m.val < n.val ∧ n.val ≤ 19) :
    ∃ rm rn, Aegis.NumTrees.num_trees m = ok rm ∧ Aegis.NumTrees.num_trees n = ok rn ∧
      rm.val < rn.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n : Std.I64) (hm : 1 ≤ m.val ∧ m.val < n.val ∧ n.val ≤ 19), ∃ rm rn, Aegis.NumTrees.num_trees m = ok rm ∧ Aegis.NumTrees.num_trees n = ok rn ∧
      rm.val < rn.val) := by
  sorry

/-- The returned value r satisfies n * r = binom(2n, n-1), where binom(a,b) denotes the binomial coefficient a! / (b! * (a-b)!).
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧
      n.val * r.val = ((binom (2 * n.val.toNat) (n.val.toNat - 1) : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧
      n.val * r.val = ((binom (2 * n.val.toNat) (n.val.toNat - 1) : Nat) : Int)) := by
  sorry

/-- The returned value r equals the number of Dyck paths of semilength n, that is, the number of sequences of exactly n up-steps (+1) and n down-steps (-1) which start at level 0, never have negative partial sum, and end at level 0.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val = (dyckPathCount n.val.toNat : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧ r.val = (dyckPathCount n.val.toNat : Int)) := by
  sorry

/-- The returned value r is odd if and only if n is one of 1, 3, 7, or 15; for all other allowed n, r is even.
  Preconditions: The integer value of the parameter n satisfies 1 <= n <= 19. -/
theorem spec_10 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19) :
    ∃ r, Aegis.NumTrees.num_trees n = ok r ∧
      (Odd r.val ↔ (n.val = 1 ∨ n.val = 3 ∨ n.val = 7 ∨ n.val = 15)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 19), ∃ r, Aegis.NumTrees.num_trees n = ok r ∧
      (Odd r.val ↔ (n.val = 1 ∨ n.val = 3 ∨ n.val = 7 ∨ n.val = 15))) := by
  sorry

end AegisSpec.NumTrees
