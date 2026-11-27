import Aegis.MaximumGood.Code.Funs

/-!
# Specifications of `Aegis.MaximumGood.maximum_good`

LeetCode problem `maximum-good-people-based-on-statements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumGood (maximum_good)

namespace AegisSpec.MaximumGood

def row (statements : Slice (alloc.vec.Vec I64)) (i : ℕ) : Option (List I64) :=
  (statements.val[i]?).map (fun r => r.val)

def rowLen (statements : Slice (alloc.vec.Vec I64)) (i : ℕ) : Option ℕ :=
  (row statements i).map (fun r => r.length)

def entry (statements : Slice (alloc.vec.Vec I64)) (i j : ℕ) : Option ℤ :=
  (row statements i).bind (fun r => (r[j]?).map (fun x => x.val))

def ValidInput (statements : Slice (alloc.vec.Vec I64)) : Prop :=
  2 ≤ statements.val.length ∧
  statements.val.length ≤ 15 ∧
  (∀ i, i < statements.val.length → rowLen statements i = some statements.val.length) ∧
  (∀ i j, i < statements.val.length → j < statements.val.length →
    entry statements i j = some 0 ∨ entry statements i j = some 1 ∨
      entry statements i j = some 2) ∧
  (∀ i, i < statements.val.length → entry statements i i = some 2)

def Valid (statements : Slice (alloc.vec.Vec I64)) (G : Finset ℕ) : Prop :=
  (∀ i ∈ G, i < statements.val.length) ∧
  (∀ i ∈ G, ∀ j, j < statements.val.length → entry statements i j = some 1 → j ∈ G) ∧
  (∀ i ∈ G, ∀ j, j < statements.val.length → entry statements i j = some 0 → j ∉ G)

noncomputable def maxGood (statements : Slice (alloc.vec.Vec I64)) : ℕ :=
  by
  classical
  exact ((Finset.range statements.val.length).powerset.filter
    (fun G => Valid statements G)).sup (fun G => G.card)

/-- The function returns a result r and r = max { |G| : G is a subset of {0, ..., n-1} and Valid(G) }, where Valid(G) means: G is a subset of {0, ..., n-1}, and for every i in G and every j with 0 <= j < n, if statements[i][j] = 1 then j in G, and if statements[i][j] = 0 then j not in G. The maximum is over all subsets satisfying Valid; the empty set is allowed.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_1 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∃ r, maximum_good statements = ok r ∧ r.val = (maxGood statements : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∃ r, maximum_good statements = ok r ∧ r.val = (maxGood statements : ℤ)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, perform an out-of-bounds access, or overflow.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_2 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∃ r, maximum_good statements = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∃ r, maximum_good statements = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_3 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      0 ≤ r.val ∧ r.val ≤ (statements.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      0 ≤ r.val ∧ r.val ≤ (statements.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset G of {0, ..., n-1} such that Valid(G) and |G| = r, where Valid(G) means: G is a subset of {0, ..., n-1}, and for every i in G and every j with 0 <= j < n, if statements[i][j] = 1 then j in G, and if statements[i][j] = 0 then j not in G.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_4 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      ∃ G : Finset ℕ, Valid statements G ∧ (G.card : ℤ) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      ∃ G : Finset ℕ, Valid statements G ∧ (G.card : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every subset G of {0, ..., n-1}, if Valid(G) then |G| <= r, where Valid(G) means: G is a subset of {0, ..., n-1}, and for every i in G and every j with 0 <= j < n, if statements[i][j] = 1 then j in G, and if statements[i][j] = 0 then j not in G.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_5 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      ∀ G : Finset ℕ, Valid statements G → (G.card : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      ∀ G : Finset ℕ, Valid statements G → (G.card : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if no nonempty subset G of {0, ..., n-1} satisfies Valid(G), where Valid(G) means: G is a subset of {0, ..., n-1}, and for every i in G and every j with 0 <= j < n, if statements[i][j] = 1 then j in G, and if statements[i][j] = 0 then j not in G.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_6 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      (r.val = 0 ↔ ¬ ∃ G : Finset ℕ, G.Nonempty ∧ Valid statements G) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      (r.val = 0 ↔ ¬ ∃ G : Finset ℕ, G.Nonempty ∧ Valid statements G)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if statements[i][j] != 0 for every i,j with 0 <= i < n and 0 <= j < n.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_7 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      (r.val = (statements.val.length : ℤ) ↔
        ∀ i j, i < statements.val.length → j < statements.val.length →
          entry statements i j ≠ some 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      (r.val = (statements.val.length : ℤ) ↔
        ∀ i j, i < statements.val.length → j < statements.val.length →
          entry statements i j ≠ some 0)) := by
  sorry

/-- Whenever the function returns a result r, if statements[i][j] = 0 for every i,j with 0 <= i < n, 0 <= j < n, and i != j, then r = 1.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_8 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      (∀ i j, i < statements.val.length → j < statements.val.length → i ≠ j →
          entry statements i j = some 0) →
      r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      (∀ i j, i < statements.val.length → j < statements.val.length → i ≠ j →
          entry statements i j = some 0) →
      r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, if there exists i with 0 <= i < n such that statements[i][j] != 1 for every j with 0 <= j < n and j != i, then r >= 1.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_9 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r →
      (∃ i, i < statements.val.length ∧
        ∀ j, j < statements.val.length → j ≠ i → entry statements i j ≠ some 1) →
      1 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r →
      (∃ i, i < statements.val.length ∧
        ∀ j, j < statements.val.length → j ≠ i → entry statements i j ≠ some 1) →
      1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if n = 2, then r >= 1.
  Preconditions: Let n = len(statements). The input satisfies the problem constraints: 2 <= n <= 15; every row statements[i] has length n; for every i,j with 0 <= i < n and 0 <= j < n, statements[i][j] is one of 0, 1, 2; and statements[i][i] = 2 for every i with 0 <= i < n. -/
theorem spec_10 (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements) :
    ∀ r, maximum_good statements = ok r → statements.val.length = 2 → 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (statements : Slice (alloc.vec.Vec I64)) (h : ValidInput statements), ∀ r, maximum_good statements = ok r → statements.val.length = 2 → 1 ≤ r.val) := by
  sorry

/-- For any two inputs statements and statements' satisfying the preconditions, if the function returns r on statements and r' on statements', and if pi is a permutation of {0, ..., n-1} such that statements'[i][j] = statements[pi(i)][pi(j)] for every i,j with 0 <= i < n and 0 <= j < n, then r = r'.
  Preconditions: Let n = len(statements) = len(statements'). Both statements and statements' satisfy the problem constraints: 2 <= n <= 15; every row has length n; all entries are one of 0, 1, 2; and all diagonal entries are 2. -/
theorem spec_11 (statements statements' : Slice (alloc.vec.Vec I64))
    (h : ValidInput statements) (h' : ValidInput statements')
    (hlen : statements.val.length = statements'.val.length)
    (pi : Equiv.Perm (Fin statements.val.length))
    (hpi : ∀ (i j : ℕ) (hi : i < statements.val.length) (hj : j < statements.val.length),
      entry statements' i j = entry statements (pi ⟨i, hi⟩).val (pi ⟨j, hj⟩).val) :
    ∀ r r', maximum_good statements = ok r → maximum_good statements' = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (statements statements' : Slice (alloc.vec.Vec I64))
    (h : ValidInput statements) (h' : ValidInput statements')
    (hlen : statements.val.length = statements'.val.length)
    (pi : Equiv.Perm (Fin statements.val.length))
    (hpi : ∀ (i j : ℕ) (hi : i < statements.val.length) (hj : j < statements.val.length),
      entry statements' i j = entry statements (pi ⟨i, hi⟩).val (pi ⟨j, hj⟩).val), ∀ r r', maximum_good statements = ok r → maximum_good statements' = ok r' → r = r') := by
  sorry

/-- For any two inputs A and B satisfying the preconditions with the same n, if for every i,j with 0 <= i < n and 0 <= j < n either A[i][j] = B[i][j] or A[i][j] = 2, and if the function returns r_A on A and r_B on B, then r_B <= r_A.
  Preconditions: Let n be the common length of A and B. Both A and B satisfy the problem constraints: 2 <= n <= 15; every row has length n; all entries are one of 0, 1, 2; and all diagonal entries are 2. -/
theorem spec_12 (A B : Slice (alloc.vec.Vec I64))
    (hA : ValidInput A) (hB : ValidInput B)
    (hlen : A.val.length = B.val.length)
    (hrel : ∀ i j, i < A.val.length → j < A.val.length →
      entry A i j = entry B i j ∨ entry A i j = some 2) :
    ∀ rA rB, maximum_good A = ok rA → maximum_good B = ok rB → rB.val ≤ rA.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec I64))
    (hA : ValidInput A) (hB : ValidInput B)
    (hlen : A.val.length = B.val.length)
    (hrel : ∀ i j, i < A.val.length → j < A.val.length →
      entry A i j = entry B i j ∨ entry A i j = some 2), ∀ rA rB, maximum_good A = ok rA → maximum_good B = ok rB → rB.val ≤ rA.val) := by
  sorry

end AegisSpec.MaximumGood
