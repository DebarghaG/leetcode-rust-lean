import Aegis.MinStartingIndex.Code.Funs

/-!
# Specifications of `Aegis.MinStartingIndex.min_starting_index`

LeetCode problem `find-the-occurrence-of-first-almost-equal-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinStartingIndex (min_starting_index)

namespace AegisSpec.MinStartingIndex

def isLowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def allLower (l : List U8) : Prop := ∀ b ∈ l, isLowerByte b

def mismatchAt (s p : List U8) (i j : Nat) : Bool :=
  match s[i + j]?, p[j]? with
  | some a, some b => a.val != b.val
  | _, _ => true

def mismatchCount (s p : List U8) (i : Nat) : Nat :=
  (List.range p.length).countP fun j => mismatchAt s p i j

def nearMatch (s p : List U8) (i : Nat) : Prop := mismatchCount s p i ≤ 1

def isNearMatchIndex (s p : List U8) (i : Nat) : Prop :=
  i ≤ s.length - p.length ∧ nearMatch s p i

def isLeastNearMatchIndex (s p : List U8) (i : Nat) : Prop :=
  isNearMatchIndex s p i ∧ ∀ k, isNearMatchIndex s p k → i ≤ k

def hasNearMatchIndex (s p : List U8) : Prop := ∃ i, isNearMatchIndex s p i

def listNMap {α β : Type} {n : Nat} (f : α → β) : Aeneas.Data.ListN.ListN α n →
    Aeneas.Data.ListN.ListN β n
  | .nil => .nil
  | .cons a rest => .cons (f a) (listNMap f rest)

def sliceMap (f : U8 → U8) (s : Slice U8) : Slice U8 :=
  ⟨s.leng, listNMap f s.list, s.bound⟩

theorem sliceMap_val (f : U8 → U8) (s : Slice U8) : (sliceMap f s).val = s.val.map f := by
  have key : ∀ {n : Nat} (l : Aeneas.Data.ListN.ListN U8 n),
      (listNMap f l).toList = l.toList.map f := by
    intro n l
    induction l with
    | nil => rfl
    | cons a rest ih => simp [listNMap, Aeneas.Data.ListN.ListN.toList, ih]
  exact key s.list

structure Precond (s pattern : Slice U8) : Prop where

  pos : 1 ≤ pattern.val.length

  le : pattern.val.length ≤ s.val.length

  bound : s.val.length ≤ 100000

  text_lower : allLower s.val

  pattern_lower : allLower pattern.val

/-- The function returns a result r and: if there exists an integer i with 0 <= i <= n-m such that the number of j with 0 <= j < m and s[i+j] != pattern[j] is at most 1, then r is the least such i; if no such i exists, then r = -1.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. (The problem statement says m < n; the weaker condition m <= n is used so that the provided test with m = n is covered.) -/
theorem spec_1
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∃ r : I64, min_starting_index s pattern = ok r ∧
      (hasNearMatchIndex s.val pattern.val →
        ∃ i : Nat, r.val = (i : Int) ∧ isLeastNearMatchIndex s.val pattern.val i) ∧
      (¬ hasNearMatchIndex s.val pattern.val → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∃ r : I64, min_starting_index s pattern = ok r ∧
      (hasNearMatchIndex s.val pattern.val →
        ∃ i : Nat, r.val = (i : Int) ∧ isLeastNearMatchIndex s.val pattern.val i) ∧
      (¬ hasNearMatchIndex s.val pattern.val → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_2
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∃ r : I64, min_starting_index s pattern = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∃ r : I64, min_starting_index s pattern = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= n-m.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_3
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∀ r : I64, min_starting_index s pattern = ok r →
      r.val = -1 ∨
        (0 ≤ r.val ∧ r.val ≤ ((s.val.length - pattern.val.length : Nat) : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∀ r : I64, min_starting_index s pattern = ok r →
      r.val = -1 ∨
        (0 ≤ r.val ∧ r.val ≤ ((s.val.length - pattern.val.length : Nat) : Int))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, the number of positions j with 0 <= j < m such that s[r+j] != pattern[j] is at most 1.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_4
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∀ r : I64, min_starting_index s pattern = ok r → 0 ≤ r.val →
      mismatchCount s.val pattern.val r.val.toNat ≤ 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∀ r : I64, min_starting_index s pattern = ok r → 0 ≤ r.val →
      mismatchCount s.val pattern.val r.val.toNat ≤ 1) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every integer j with 0 <= j < r, the number of positions k with 0 <= k < m such that s[j+k] != pattern[k] is at least 2.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_5
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∀ r : I64, min_starting_index s pattern = ok r → 0 ≤ r.val →
      ∀ j : Nat, j < r.val.toNat → 2 ≤ mismatchCount s.val pattern.val j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∀ r : I64, min_starting_index s pattern = ok r → 0 ≤ r.val →
      ∀ j : Nat, j < r.val.toNat → 2 ≤ mismatchCount s.val pattern.val j) := by
  sorry

/-- Whenever the function returns a result r with r = -1, for every integer i with 0 <= i <= n-m, the number of positions j with 0 <= j < m such that s[i+j] != pattern[j] is at least 2.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_6
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∀ r : I64, min_starting_index s pattern = ok r → r.val = -1 →
      ∀ i : Nat, i ≤ s.val.length - pattern.val.length →
        2 ≤ mismatchCount s.val pattern.val i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∀ r : I64, min_starting_index s pattern = ok r → r.val = -1 →
      ∀ i : Nat, i ≤ s.val.length - pattern.val.length →
        2 ≤ mismatchCount s.val pattern.val i) := by
  sorry

/-- Whenever the function returns a result r, if there exists an integer i with 0 <= i <= n-m such that the number of j with 0 <= j < m and s[i+j] != pattern[j] is at most 1, then r >= 0.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_7
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∀ r : I64, min_starting_index s pattern = ok r →
      hasNearMatchIndex s.val pattern.val → 0 ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∀ r : I64, min_starting_index s pattern = ok r →
      hasNearMatchIndex s.val pattern.val → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if for every integer i with 0 <= i <= n-m the number of j with 0 <= j < m and s[i+j] != pattern[j] is at least 2, then r = -1.
  Preconditions: Let n = len(s) and m = len(pattern). The inputs satisfy 1 <= m <= n <= 100000, and every byte of s and pattern is an ASCII code of a lowercase English letter. -/
theorem spec_8
    (s pattern : Slice U8) (hpre : Precond s pattern) :
    ∀ r : I64, min_starting_index s pattern = ok r →
      (∀ i : Nat, i ≤ s.val.length - pattern.val.length →
        2 ≤ mismatchCount s.val pattern.val i) →
      r.val = -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s pattern : Slice U8) (hpre : Precond s pattern), ∀ r : I64, min_starting_index s pattern = ok r →
      (∀ i : Nat, i ≤ s.val.length - pattern.val.length →
        2 ≤ mismatchCount s.val pattern.val i) →
      r.val = -1) := by
  sorry

/-- Whenever the function returns a result r on the pair (s, pattern), it returns the same result r on the pair (f(s), f(pattern)).
  Preconditions: Let n = len(s) and m = len(pattern), with 1 <= m <= n <= 100000, and let s and pattern consist of lowercase English letters. Let f be any bijection (permutation) of the 26 lowercase letters, and let f(s) and f(pattern) be obtained by applying f to every byte. -/
theorem spec_9
    (s pattern : Slice U8) (f g : U8 → U8) (hpre : Precond s pattern)
    (hf : ∀ b, isLowerByte b → isLowerByte (f b))
    (hgf : ∀ b, isLowerByte b → g (f b) = b)
    (hfg : ∀ b, isLowerByte b → f (g b) = b) :
    ∀ r : I64, min_starting_index s pattern = ok r →
      min_starting_index (sliceMap f s) (sliceMap f pattern) = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s pattern : Slice U8) (f g : U8 → U8) (hpre : Precond s pattern)
    (hf : ∀ b, isLowerByte b → isLowerByte (f b))
    (hgf : ∀ b, isLowerByte b → g (f b) = b)
    (hfg : ∀ b, isLowerByte b → f (g b) = b), ∀ r : I64, min_starting_index s pattern = ok r →
      min_starting_index (sliceMap f s) (sliceMap f pattern) = ok r) := by
  sorry

end AegisSpec.MinStartingIndex
