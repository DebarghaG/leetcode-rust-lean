import Mathlib.Data.Real.Basic
import Aegis.JudgePoint24.Code.Funs

/-!
# Specifications of `Aegis.JudgePoint24.judge_point24`

LeetCode problem `24-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.JudgePoint24

inductive Expr where

  | leaf (n : ℤ)

  | add (l r : Expr)

  | sub (l r : Expr)

  | mul (l r : Expr)

  | div (l r : Expr)

namespace Expr

def leaves : Expr → List ℤ
  | leaf n => [n]
  | add l r => l.leaves ++ r.leaves
  | sub l r => l.leaves ++ r.leaves
  | mul l r => l.leaves ++ r.leaves
  | div l r => l.leaves ++ r.leaves

noncomputable def eval : Expr → Option ℝ
  | leaf n => some (n : ℝ)
  | add l r =>
    match eval l, eval r with
    | some x, some y => some (x + y)
    | _, _ => none
  | sub l r =>
    match eval l, eval r with
    | some x, some y => some (x - y)
    | _, _ => none
  | mul l r =>
    match eval l, eval r with
    | some x, some y => some (x * y)
    | _, _ => none
  | div l r =>
    match eval l, eval r with
    | some x, some y => if y = 0 then none else some (x / y)
    | _, _ => none

end Expr

/-- The function returns a result r (it does not fail), and r = true if and only if there exists a binary expression tree with the following properties: (1) it has exactly 4 leaves, labeled by the four elements of cards in some order, each used exactly once; (2) each internal node is labeled by one of '+', '-', '*', '/'; (3) every internal node has exactly two children (so the tree is a full binary tree with 3 internal nodes); (4) the tree is evaluated using real arithmetic, where for '/' the divisor must be non-zero; (5) the evaluated value is exactly 24. Equivalently, the four numbers can be combined using the allowed operations and parentheses to yield 24, using each number exactly once.
  Preconditions: cards is a slice of length 4, and for every index i with 0 <= i < 4, 1 <= cards[i] <= 9. -/
theorem spec_1 (cards : Slice Std.I64)
    (hlen : cards.val.length = 4)
    (hrange : ∀ x ∈ cards.val, 1 ≤ IScalar.val x ∧ IScalar.val x ≤ 9) :
    ∃ r, Aegis.JudgePoint24.judge_point24 cards = Result.ok r ∧
      (r = true ↔
        ∃ e : Expr, e.leaves.Perm (cards.val.map IScalar.val) ∧ e.eval = some 24) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cards : Slice Std.I64)
    (hlen : cards.val.length = 4)
    (hrange : ∀ x ∈ cards.val, 1 ≤ IScalar.val x ∧ IScalar.val x ≤ 9), ∃ r, Aegis.JudgePoint24.judge_point24 cards = Result.ok r ∧
      (r = true ↔
        ∃ e : Expr, e.leaves.Perm (cards.val.map IScalar.val) ∧ e.eval = some 24)) := by
  sorry

/-- The function returns the same result on both inputs: judge_point24(cards1) = judge_point24(cards2).
  Preconditions: cards1 and cards2 are two slices of length 4, and for every index i with 0 <= i < 4, 1 <= cards1[i] <= 9 and 1 <= cards2[i] <= 9. The multiset of elements of cards1 equals the multiset of elements of cards2 (i.e., cards2 is a permutation of cards1). -/
theorem spec_2 (cards1 cards2 : Slice Std.I64)
    (hlen1 : cards1.val.length = 4)
    (hlen2 : cards2.val.length = 4)
    (hrange1 : ∀ x ∈ cards1.val, 1 ≤ IScalar.val x ∧ IScalar.val x ≤ 9)
    (hrange2 : ∀ x ∈ cards2.val, 1 ≤ IScalar.val x ∧ IScalar.val x ≤ 9)
    (hperm : cards1.val.Perm cards2.val) :
    Aegis.JudgePoint24.judge_point24 cards1 = Aegis.JudgePoint24.judge_point24 cards2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cards1 cards2 : Slice Std.I64)
    (hlen1 : cards1.val.length = 4)
    (hlen2 : cards2.val.length = 4)
    (hrange1 : ∀ x ∈ cards1.val, 1 ≤ IScalar.val x ∧ IScalar.val x ≤ 9)
    (hrange2 : ∀ x ∈ cards2.val, 1 ≤ IScalar.val x ∧ IScalar.val x ≤ 9)
    (hperm : cards1.val.Perm cards2.val), Aegis.JudgePoint24.judge_point24 cards1 = Aegis.JudgePoint24.judge_point24 cards2) := by
  sorry

/-- The function returns false.
  Preconditions: cards is a slice of length 4 equal to [1,1,1,1]. -/
theorem spec_3 (cards : Slice Std.I64)
    (hcards : cards.val = [1#i64, 1#i64, 1#i64, 1#i64]) :
    Aegis.JudgePoint24.judge_point24 cards = Result.ok false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cards : Slice Std.I64)
    (hcards : cards.val = [1#i64, 1#i64, 1#i64, 1#i64]), Aegis.JudgePoint24.judge_point24 cards = Result.ok false) := by
  sorry

/-- The function returns true.
  Preconditions: cards is a slice of length 4 equal to [4,1,8,7]. -/
theorem spec_4 (cards : Slice Std.I64)
    (hcards : cards.val = [4#i64, 1#i64, 8#i64, 7#i64]) :
    Aegis.JudgePoint24.judge_point24 cards = Result.ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cards : Slice Std.I64)
    (hcards : cards.val = [4#i64, 1#i64, 8#i64, 7#i64]), Aegis.JudgePoint24.judge_point24 cards = Result.ok true) := by
  sorry

end AegisSpec.JudgePoint24
