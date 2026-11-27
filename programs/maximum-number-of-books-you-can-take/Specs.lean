import Aegis.MaximumBooks.Code.Funs

/-!
# Specifications of `Aegis.MaximumBooks.maximum_books`

LeetCode problem `maximum-number-of-books-you-can-take`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumBooks

open scoped BigOperators

open Aegis.MaximumBooks (maximum_books)

def getVal (books : Slice I64) (i : Nat) : Int :=
  match books.val[i]? with
  | some b => b.val
  | none => 0

theorem getVal_of_lt {books : Slice I64} {i : Nat} (h : i < books.val.length) :
    getVal books i = (books.val[i]'h).val := by
  unfold getVal
  rw [List.getElem?_eq_getElem h]

def ValidInput (books : Slice I64) : Prop :=
  1 ≤ books.val.length ∧ books.val.length ≤ 100000 ∧
    ∀ i, i < books.val.length → 0 ≤ getVal books i ∧ getVal books i ≤ 100000

def totalSum (books : Slice I64) : Int :=
  ∑ i ∈ Finset.range books.val.length, getVal books i

def maxEntry (books : Slice I64) : Int :=
  books.val.foldr (fun b acc => max b.val acc) 0

def StrictIncOn (books : Slice I64) (l r : Nat) : Prop :=
  ∀ i, l ≤ i → i < r → getVal books i < getVal books (i + 1)

def choiceSum (l r : Nat) (x : Nat → Int) : Int :=
  ∑ i ∈ Finset.Ico l (r + 1), x i

def IsChoice (books : Slice I64) (l r : Nat) (x : Nat → Int) : Prop :=
  l ≤ r ∧ r < books.val.length ∧
    (∀ i, l ≤ i → i ≤ r → 0 ≤ x i ∧ x i ≤ getVal books i) ∧
    (∀ i, l ≤ i → i < r → x i < x (i + 1))

def IsMaxChoiceSum (books : Slice I64) (S : Int) : Prop :=
  (∃ l r x, IsChoice books l r x ∧ choiceSum l r x = S) ∧
    ∀ l r x, IsChoice books l r x → choiceSum l r x ≤ S

def triCap (m M : Int) : Int :=
  m * M - m * (m - 1) / 2

/-- The function returns a result R, and R equals the maximum, over all choices (l, r, x) such that 0 <= l <= r < n, x is an integer sequence indexed by l..r, 0 <= x_i <= books[i] for every i with l <= i <= r, and x_i < x_{i+1} for every i with l <= i < r, of the total sum_{i=l}^r x_i.
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_1 (books : Slice I64) (h : ValidInput books) :
    ∃ R, maximum_books books = ok R ∧ IsMaxChoiceSum books R.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∃ R, maximum_books books = ok R ∧ IsMaxChoiceSum books R.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result R; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_2 (books : Slice I64) (h : ValidInput books) :
    ∃ R, maximum_books books = ok R := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∃ R, maximum_books books = ok R) := by
  sorry

/-- Whenever the function returns a result R, for every choice (l, r, x) satisfying 0 <= l <= r < n, 0 <= x_i <= books[i] for all i with l <= i <= r, and x_i < x_{i+1} for all i with l <= i < r, we have sum_{i=l}^r x_i <= R.
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_3 (books : Slice I64) (h : ValidInput books) :
    ∀ R, maximum_books books = ok R →
      ∀ l r x, IsChoice books l r x → choiceSum l r x ≤ R.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∀ R, maximum_books books = ok R →
      ∀ l r x, IsChoice books l r x → choiceSum l r x ≤ R.val) := by
  sorry

/-- Whenever the function returns a result R, there exists a choice (l, r, x) satisfying 0 <= l <= r < n, 0 <= x_i <= books[i] for all i with l <= i <= r, and x_i < x_{i+1} for all i with l <= i < r, such that sum_{i=l}^r x_i = R.
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_4 (books : Slice I64) (h : ValidInput books) :
    ∀ R, maximum_books books = ok R →
      ∃ l r x, IsChoice books l r x ∧ choiceSum l r x = R.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∀ R, maximum_books books = ok R →
      ∃ l r x, IsChoice books l r x ∧ choiceSum l r x = R.val) := by
  sorry

/-- Whenever the function returns a result R, for every i with 0 <= i < n, we have R >= books[i].
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_5 (books : Slice I64) (h : ValidInput books) :
    ∀ R, maximum_books books = ok R →
      ∀ i, i < books.val.length → getVal books i ≤ R.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∀ R, maximum_books books = ok R →
      ∀ i, i < books.val.length → getVal books i ≤ R.val) := by
  sorry

/-- Whenever the function returns a result R, we have R <= sum_{i=0}^{n-1} books[i].
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_6 (books : Slice I64) (h : ValidInput books) :
    ∀ R, maximum_books books = ok R → R.val ≤ totalSum books := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∀ R, maximum_books books = ok R → R.val ≤ totalSum books) := by
  sorry

/-- The function returns a result R and R = sum_{i=0}^{n-1} books[i].
  Preconditions: Let n = len(books). Assume 2 <= n <= 100000, 0 <= books[i] <= 100000 for every i with 0 <= i < n, and books[i] < books[i+1] for every i with 0 <= i < n-1. -/
theorem spec_7 (books : Slice I64)
    (hn : 2 ≤ books.val.length) (hn' : books.val.length ≤ 100000)
    (hb : ∀ i, i < books.val.length → 0 ≤ getVal books i ∧ getVal books i ≤ 100000)
    (hinc : StrictIncOn books 0 (books.val.length - 1)) :
    ∃ R, maximum_books books = ok R ∧ R.val = totalSum books := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (books : Slice I64)
    (hn : 2 ≤ books.val.length) (hn' : books.val.length ≤ 100000)
    (hb : ∀ i, i < books.val.length → 0 ≤ getVal books i ∧ getVal books i ≤ 100000)
    (hinc : StrictIncOn books 0 (books.val.length - 1)), ∃ R, maximum_books books = ok R ∧ R.val = totalSum books) := by
  sorry

/-- Whenever the function returns a result R, for every l and r with 0 <= l < r < n such that books[i] < books[i+1] for every i with l <= i < r, we have R >= sum_{i=l}^r books[i].
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_8 (books : Slice I64) (h : ValidInput books) :
    ∀ R, maximum_books books = ok R →
      ∀ l r, l < r → r < books.val.length → StrictIncOn books l r →
        (∑ i ∈ Finset.Ico l (r + 1), getVal books i) ≤ R.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∀ R, maximum_books books = ok R →
      ∀ l r, l < r → r < books.val.length → StrictIncOn books l r →
        (∑ i ∈ Finset.Ico l (r + 1), getVal books i) ≤ R.val) := by
  sorry

/-- The function returns a result R and R = m*c - m*(m-1)/2, where m = min(n, c+1).
  Preconditions: Let n = len(books). Assume 2 <= n <= 100000, and there exists an integer c with 0 <= c <= 100000 such that books[i] = c for every i with 0 <= i < n. -/
theorem spec_9 (books : Slice I64) (c : Int)
    (hn : 2 ≤ books.val.length) (hn' : books.val.length ≤ 100000)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 100000)
    (hall : ∀ i, i < books.val.length → getVal books i = c) :
    ∃ R, maximum_books books = ok R ∧
      R.val = triCap (min (books.val.length : Int) (c + 1)) c := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (books : Slice I64) (c : Int)
    (hn : 2 ≤ books.val.length) (hn' : books.val.length ≤ 100000)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 100000)
    (hall : ∀ i, i < books.val.length → getVal books i = c), ∃ R, maximum_books books = ok R ∧
      R.val = triCap (min (books.val.length : Int) (c + 1)) c) := by
  sorry

/-- Whenever the function returns a result R, we have R <= m0*M - m0*(m0-1)/2.
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. Let M = max_{0 <= i < n} books[i] and m0 = min(n, M+1). -/
theorem spec_10 (books : Slice I64) (h : ValidInput books) :
    ∀ R, maximum_books books = ok R →
      R.val ≤ triCap (min (books.val.length : Int) (maxEntry books + 1)) (maxEntry books) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (books : Slice I64) (h : ValidInput books), ∀ R, maximum_books books = ok R →
      R.val ≤ triCap (min (books.val.length : Int) (maxEntry books + 1)) (maxEntry books)) := by
  sorry

/-- For every array books' of length n such that 0 <= books'[i] <= 100000 and books[i] <= books'[i] for every i with 0 <= i < n, if R is the result returned by maximum_books(books) and R' is the result returned by maximum_books(books'), then R <= R'.
  Preconditions: Let n = len(books). Assume 1 <= n <= 100000 and 0 <= books[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_11 (books books' : Slice I64) (h : ValidInput books)
    (hlen : books'.val.length = books.val.length)
    (hb' : ∀ i, i < books'.val.length → 0 ≤ getVal books' i ∧ getVal books' i ≤ 100000)
    (hle : ∀ i, i < books.val.length → getVal books i ≤ getVal books' i) :
    ∀ R R', maximum_books books = ok R → maximum_books books' = ok R' → R.val ≤ R'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (books books' : Slice I64) (h : ValidInput books)
    (hlen : books'.val.length = books.val.length)
    (hb' : ∀ i, i < books'.val.length → 0 ≤ getVal books' i ∧ getVal books' i ≤ 100000)
    (hle : ∀ i, i < books.val.length → getVal books i ≤ getVal books' i), ∀ R R', maximum_books books = ok R → maximum_books books' = ok R' → R.val ≤ R'.val) := by
  sorry

end AegisSpec.MaximumBooks
