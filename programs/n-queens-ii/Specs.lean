import Aegis.TotalNQueens.Code.Funs

/-!
# Specifications of `Aegis.TotalNQueens.total_n_queens`

LeetCode problem `n-queens-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TotalNQueens

  def IsPlacement (n : ℤ) (q : List ℤ) : Prop :=
    q.length = n.toNat ∧
      (∀ i : Fin q.length, 0 ≤ q.get i ∧ q.get i < n) ∧
      (∀ i j : Fin q.length, i < j →
        q.get i ≠ q.get j ∧
          q.get i - q.get j ≠ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ∧
          q.get i - q.get j ≠ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))

  instance instDecidableIsPlacement (n : ℤ) (q : List ℤ) : Decidable (IsPlacement n q) := by
    unfold IsPlacement
    infer_instance

  def candidates (n : ℤ) : Finset (List ℤ) :=
    (Finset.univ : Finset (Fin n.toNat → Fin n.toNat)).image
      (fun f => List.ofFn (fun i => (((f i : ℕ) : ℤ))))

  def V (n : ℤ) : Finset (List ℤ) :=
    (candidates n).filter (fun q => IsPlacement n q)

  def numSolutions (n : ℤ) : ℕ := (V n).card

  /-- Let V(n) be the set of all sequences q = (q[0],...,q[n-1]) such that each q[i] is in {0,1,...,n-1} and for all 0 <= i < j < n we have q[i] != q[j], q[i] - q[j] != i - j, and q[i] - q[j] != j - i. The function returns a result r and r = |V(n)|. Thus r is the number of ways to place n non-attacking queens on an n x n board, row i having its queen in column q[i], with solutions that differ by any board symmetry counted separately unless they are the same sequence.
    Preconditions: 1 <= n <= 9, where n is the integer value of the Std.I64 argument. -/
  theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = ((V n.val).card : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = ((V n.val).card : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: 1 <= n <= 9. -/
  theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: 1 <= n <= 9. -/
  theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9) :
      ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9), ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= n!, where n! = 1*2*...*n.
    Preconditions: 1 <= n <= 9. -/
  theorem spec_4 (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9) :
      ∀ r : Std.I64,
        Aegis.TotalNQueens.total_n_queens n = ok r → r.val ≤ ((Nat.factorial n.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9), ∀ r : Std.I64,
          Aegis.TotalNQueens.total_n_queens n = ok r → r.val ≤ ((Nat.factorial n.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 352.
    Preconditions: 1 <= n <= 9. -/
  theorem spec_5 (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9) :
      ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → r.val ≤ 352 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9), ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → r.val ≤ 352) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: n = 1. -/
  theorem spec_6 (n : Std.I64) (hn : n.val = 1) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: n = 2 or n = 3. -/
  theorem spec_7 (n : Std.I64) (hn : n.val = 2 ∨ n.val = 3) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2 ∨ n.val = 3), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 2. Moreover V(4) consists exactly of the two sequences (1,3,0,2) and (2,0,3,1), where the i-th component is the column of the queen in row i.
    Preconditions: n = 4. -/
  theorem spec_8 (n : Std.I64) (hn : n.val = 4) :
      (∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 2) ∧
        (∀ q : List ℤ,
          IsPlacement n.val q ↔ q = ([1, 3, 0, 2] : List ℤ) ∨ q = ([2, 0, 3, 1] : List ℤ)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 4), (∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 2) ∧
          (∀ q : List ℤ,
            IsPlacement n.val q ↔ q = ([1, 3, 0, 2] : List ℤ) ∨ q = ([2, 0, 3, 1] : List ℤ))) := by
    sorry

  /-- The function returns a result r and r = 4.
    Preconditions: n = 6. -/
  theorem spec_9 (n : Std.I64) (hn : n.val = 6) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 4 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 6), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 4) := by
    sorry

  /-- The function returns a result r and r = 92.
    Preconditions: n = 8. -/
  theorem spec_10 (n : Std.I64) (hn : n.val = 8) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 92 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 8), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 92) := by
    sorry

  /-- The function returns a result r and r = 352.
    Preconditions: n = 9. -/
  theorem spec_11 (n : Std.I64) (hn : n.val = 9) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 352 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 9), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 352) := by
    sorry

  /-- Whenever the function returns a result r, r is even.
    Preconditions: 2 <= n <= 9. -/
  theorem spec_12 (n : Std.I64) (h2 : 2 ≤ n.val) (h9 : n.val ≤ 9) :
      ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → Even r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (h2 : 2 ≤ n.val) (h9 : n.val ≤ 9), ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → Even r.val) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if V(n) is nonempty; equivalently, r = 0 if and only if there is no valid n-queen placement.
    Preconditions: 1 <= n <= 9. -/
  theorem spec_13 (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9) :
      ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → (0 < r.val ↔ (V n.val).Nonempty) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h9 : n.val ≤ 9), ∀ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r → (0 < r.val ↔ (V n.val).Nonempty)) := by
    sorry

  /-- The function returns a result r and r = 10.
    Preconditions: n = 5. -/
  theorem spec_14 (n : Std.I64) (hn : n.val = 5) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 10 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 5), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 10) := by
    sorry

  /-- The function returns a result r and r = 40.
    Preconditions: n = 7. -/
  theorem spec_15 (n : Std.I64) (hn : n.val = 7) :
      ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 40 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 7), ∃ r : Std.I64, Aegis.TotalNQueens.total_n_queens n = ok r ∧ r.val = 40) := by
    sorry

  end AegisSpec.TotalNQueens
