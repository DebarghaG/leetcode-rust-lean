import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-deletions-to-make-array-divisible`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def values (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def DividesAll (s : Slice Std.I64) (x : ℤ) : Prop := ∀ y ∈ values s, y % x = 0

def IsLeastElem (a : ℤ) (l : List ℤ) : Prop := a ∈ l ∧ ∀ z ∈ l, a ≤ z

def SubMultiset (S T : List ℤ) : Prop := ∀ a : ℤ, S.count a ≤ T.count a

def DeleteExactly (d : ℕ) (S T : List ℤ) : Prop :=
  SubMultiset S T ∧ S.length + d = T.length

def candidateSet (nums numsDivide : Slice Std.I64) : Set ℤ :=
  {x | x ∈ values nums ∧ DividesAll numsDivide x}

def gcdOfList (l : List ℤ) : ℤ := ↑(l.foldr (fun a acc => Nat.gcd a.natAbs acc) 0)

def candidateSetGcd (nums numsDivide : Slice Std.I64) : Set ℤ :=
  {x | x ∈ values nums ∧ gcdOfList (values numsDivide) % x = 0}

def IsReindexOf (l' l : List ℤ) : Prop :=
  ∃ p : Equiv.Perm (Fin l.length), ∀ i : Fin l.length, l'[i.1]? = some (l.get (p i))

def ValidInput (nums numsDivide : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
  1 ≤ numsDivide.val.length ∧ numsDivide.val.length ≤ 100000 ∧
  (∀ x ∈ values nums, 1 ≤ x) ∧ (∀ y ∈ values numsDivide, 1 ≤ y)

/-- Whenever the function returns a result r, let C be the set of integers x such that (a) there exists i with 0 <= i < len(nums) and nums[i] = x, and (b) for every j with 0 <= j < len(numsDivide), numsDivide[j] % x = 0. If C is empty then r = -1. If C is nonempty and m = min(C), then r is the number of indices i with 0 <= i < len(nums) and nums[i] < m.
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_1 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      (candidateSet nums numsDivide = ∅ → r.val = -1) ∧
      (∀ m : ℤ, IsLeast (candidateSet nums numsDivide) m →
        r.val = ↑((values nums).countP (fun y => decide (y < m)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      (candidateSet nums numsDivide = ∅ → r.val = -1) ∧
      (∀ m : ℤ, IsLeast (candidateSet nums numsDivide) m →
        r.val = ↑((values nums).countP (fun y => decide (y < m))))) := by
  sorry

/-- Under the preconditions, the function returns a result r (it does not fail by overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_2 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r < len(nums).
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_3 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      r.val = -1 ∨ 0 ≤ r.val ∧ r.val < (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      r.val = -1 ∨ 0 ≤ r.val ∧ r.val < (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if the least value occurring in nums divides every element of numsDivide. Equivalently, if a is the value with a = nums[i] for some i and nums[k] >= a for every k, then r = 0 if and only if numsDivide[j] % a = 0 for every j with 0 <= j < len(numsDivide).
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_4 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ a : ℤ, a ∈ values nums → (∀ z ∈ values nums, a ≤ z) →
        (r.val = 0 ↔ DividesAll numsDivide a) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ a : ℤ, a ∈ values nums → (∀ z ∈ values nums, a ≤ z) →
        (r.val = 0 ↔ DividesAll numsDivide a)) := by
  sorry

/-- Whenever the function returns a result r, r != -1 if and only if there exists an index i with 0 <= i < len(nums) such that for every j with 0 <= j < len(numsDivide), numsDivide[j] % nums[i] = 0.
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_5 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      (r.val ≠ -1 ↔ ∃ x : ℤ, x ∈ values nums ∧ DividesAll numsDivide x) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      (r.val ≠ -1 ↔ ∃ x : ℤ, x ∈ values nums ∧ DividesAll numsDivide x)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a sub-multiset S of nums, obtained by deleting exactly r entries from nums, such that len(S) = len(nums) - r, S is nonempty, and, writing a for the least element of S, for every j with 0 <= j < len(numsDivide), numsDivide[j] % a = 0.
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_6 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      r.val ≠ -1 →
        ∃ (S : List ℤ) (a : ℤ), S ≠ [] ∧ IsLeastElem a S ∧
          DeleteExactly r.val.toNat S (values nums) ∧ DividesAll numsDivide a := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      r.val ≠ -1 →
        ∃ (S : List ℤ) (a : ℤ), S ≠ [] ∧ IsLeastElem a S ∧
          DeleteExactly r.val.toNat S (values nums) ∧ DividesAll numsDivide a) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every integer d with 0 <= d < r there is no nonempty sub-multiset S of nums obtained by deleting exactly d entries from nums whose least element divides every element of numsDivide. Equivalently, for every such S there exists j with 0 <= j < len(numsDivide) such that numsDivide[j] % min(S) != 0.
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_7 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      r.val ≠ -1 →
        ∀ (d : ℕ) (S : List ℤ) (a : ℤ), (↑d : ℤ) < r.val →
          DeleteExactly d S (values nums) → S ≠ [] → IsLeastElem a S →
          ¬ DividesAll numsDivide a := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      r.val ≠ -1 →
        ∀ (d : ℕ) (S : List ℤ) (a : ℤ), (↑d : ℤ) < r.val →
          DeleteExactly d S (values nums) → S ≠ [] → IsLeastElem a S →
          ¬ DividesAll numsDivide a) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(nums) such that nums[i] divides every numsDivide[j] for 0 <= j < len(numsDivide), then r != -1 and r <= the number of indices k with 0 <= k < len(nums) and nums[k] < nums[i].
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_8 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ a : ℤ, a ∈ values nums → DividesAll numsDivide a →
        r.val ≠ -1 ∧ r.val ≤ ↑((values nums).countP (fun y => decide (y < a))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ a : ℤ, a ∈ values nums → DividesAll numsDivide a →
        r.val ≠ -1 ∧ r.val ≤ ↑((values nums).countP (fun y => decide (y < a)))) := by
  sorry

/-- Whenever the function returns a result r, let g be the greatest common divisor of all entries of numsDivide. Let C_g be the set of integers x such that x = nums[i] for some i with 0 <= i < len(nums) and g % x = 0. If C_g is empty then r = -1; otherwise r is the number of indices i with 0 <= i < len(nums) and nums[i] < min(C_g).
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_9 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      (candidateSetGcd nums numsDivide = ∅ → r.val = -1) ∧
      (∀ m : ℤ, IsLeast (candidateSetGcd nums numsDivide) m →
        r.val = ↑((values nums).countP (fun y => decide (y < m)))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      (candidateSetGcd nums numsDivide = ∅ → r.val = -1) ∧
      (∀ m : ℤ, IsLeast (candidateSetGcd nums numsDivide) m →
        r.val = ↑((values nums).countP (fun y => decide (y < m))))) := by
  sorry

/-- Whenever the function returns a result r for (nums, numsDivide), for every slice nums' with len(nums') = len(nums) such that there is a bijection p from {0,...,len(nums)-1} to itself with nums'[i] = nums[p(i)] for all i, if the function returns a result r' for (nums', numsDivide), then r' = r.
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_10 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ nums' : Slice Std.I64, (values nums').length = (values nums).length →
        IsReindexOf (values nums') (values nums) →
        ∀ r' : Std.I64, Aegis.MinOperations.min_operations nums' numsDivide = ok r' →
          r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ nums' : Slice Std.I64, (values nums').length = (values nums).length →
        IsReindexOf (values nums') (values nums) →
        ∀ r' : Std.I64, Aegis.MinOperations.min_operations nums' numsDivide = ok r' →
          r' = r) := by
  sorry

/-- Whenever the function returns a result r for (nums, numsDivide), for every slice numsDivide' with len(numsDivide') = len(numsDivide) such that there is a bijection p from {0,...,len(numsDivide)-1} to itself with numsDivide'[i] = numsDivide[p(i)] for all i, if the function returns a result r' for (nums, numsDivide'), then r' = r.
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. -/
theorem spec_11 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ numsDivide' : Slice Std.I64,
        (values numsDivide').length = (values numsDivide).length →
        IsReindexOf (values numsDivide') (values numsDivide) →
        ∀ r' : Std.I64, Aegis.MinOperations.min_operations nums numsDivide' = ok r' →
          r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ∀ numsDivide' : Slice Std.I64,
        (values numsDivide').length = (values numsDivide).length →
        IsReindexOf (values numsDivide') (values numsDivide) →
        ∀ r' : Std.I64, Aegis.MinOperations.min_operations nums numsDivide' = ok r' →
          r' = r) := by
  sorry

/-- Whenever the function returns a result r: if there is no nonempty sub-multiset S of nums whose least element divides every numsDivide[j] for 0 <= j < len(numsDivide), then r = -1. Otherwise, r = len(nums) - M, where M is the maximum length of a nonempty sub-multiset S of nums such that the least element of S divides every numsDivide[j] for 0 <= j < len(numsDivide).
  Preconditions: 1 <= len(nums) <= 100000 and 1 <= len(numsDivide) <= 100000; for every i with 0 <= i < len(nums), nums[i] >= 1; for every j with 0 <= j < len(numsDivide), numsDivide[j] >= 1. All values are 64-bit integers and all indices are 0-based. No upper bound on the positive values is assumed. Here a sub-multiset of nums means a selection of elements whose multiplicities are at most their multiplicities in nums. -/
theorem spec_12 (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide) :
    ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ((∀ (S : List ℤ) (a : ℤ), SubMultiset S (values nums) → S ≠ [] → IsLeastElem a S →
          ¬ DividesAll numsDivide a) → r.val = -1) ∧
      (∀ M : ℕ,
        (∀ (S : List ℤ) (a : ℤ), SubMultiset S (values nums) → S ≠ [] → IsLeastElem a S →
          DividesAll numsDivide a → S.length ≤ M) →
        (∃ (S : List ℤ) (a : ℤ), S ≠ [] ∧ IsLeastElem a S ∧ DividesAll numsDivide a ∧
          S.length = M) →
        r.val = ((values nums).length : ℤ) - (M : ℤ)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums numsDivide : Slice Std.I64) (h : ValidInput nums numsDivide), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums numsDivide = ok r →
      ((∀ (S : List ℤ) (a : ℤ), SubMultiset S (values nums) → S ≠ [] → IsLeastElem a S →
          ¬ DividesAll numsDivide a) → r.val = -1) ∧
      (∀ M : ℕ,
        (∀ (S : List ℤ) (a : ℤ), SubMultiset S (values nums) → S ≠ [] → IsLeastElem a S →
          DividesAll numsDivide a → S.length ≤ M) →
        (∃ (S : List ℤ) (a : ℤ), S ≠ [] ∧ IsLeastElem a S ∧ DividesAll numsDivide a ∧
          S.length = M) →
        r.val = ((values nums).length : ℤ) - (M : ℤ))) := by
  sorry

end AegisSpec.MinOperations
