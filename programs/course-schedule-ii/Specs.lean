import Aegis.FindOrder.Code.Funs

/-!
# Specifications of `Aegis.FindOrder.find_order`

LeetCode problem `course-schedule-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindOrder

def contents (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

@[simp]
theorem contents_length (v : alloc.vec.Vec Std.I64) :
    (contents v).length = v.val.length := by
  simp [contents]

def idxOf (x : Int) : List Int → Nat
  | [] => 0
  | y :: t => if y = x then 0 else idxOf x t + 1

def IsPermOfRange (s : List Int) (n : Int) : Prop :=
  s.length = n.toNat ∧ ∀ c : Int, c ∈ s ↔ 0 ≤ c ∧ c < n

def pairOf (v : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
  match contents v with
  | a :: b :: _ => some (a, b)
  | _ => none

def pairsOf (prerequisites : List (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  prerequisites.filterMap pairOf

def PrereqOrder (s : List Int) (prerequisites : List (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ v ∈ prerequisites, ∀ a b : Int, contents v = [a, b] → idxOf b s < idxOf a s

def HasTopoOrder (n : Int) (prerequisites : List (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ s : List Int, IsPermOfRange s n ∧ PrereqOrder s prerequisites

def HasEdge (prerequisites : List (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
  ∃ v ∈ prerequisites, contents v = [a, b]

def IsCycle (prerequisites : List (alloc.vec.Vec Std.I64)) (c : List Int) : Prop :=
  1 ≤ c.length ∧ c.Nodup ∧
    ∀ i : Nat, i < c.length → ∀ y : Int, c[i]? = some y →
      ∃ x : Int, c[(i + 1) % c.length]? = some x ∧ HasEdge prerequisites x y

structure Preconditions (numCourses : Std.I64)
    (prerequisites : Slice (alloc.vec.Vec Std.I64)) : Prop where
  courses_lower : 1 ≤ numCourses.val
  courses_upper : numCourses.val ≤ 2000
  rows_length : ∀ v ∈ prerequisites.val, ∃ a b : Int, contents v = [a, b]
  left_in_range :
    ∀ v ∈ prerequisites.val, ∀ a b : Int,
      contents v = [a, b] → 0 ≤ a ∧ a < numCourses.val
  right_in_range :
    ∀ v ∈ prerequisites.val, ∀ a b : Int,
      contents v = [a, b] → 0 ≤ b ∧ b < numCourses.val
  rows_differ : ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] → a ≠ b
  rows_distinct : (pairsOf prerequisites.val).Nodup

/-- The function returns a result r. If there exists a sequence s of length numCourses that is a permutation of {0, 1, ..., numCourses-1} and for every i with 0 <= i < len(prerequisites), if prerequisites[i][0] = a and prerequisites[i][1] = b, then the index of b in s is less than the index of a in s, then r is such a sequence. Otherwise, r is the empty vector (len(r) = 0).
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_1 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r ∧
        (HasTopoOrder numCourses.val prerequisites.val →
            IsPermOfRange (contents r) numCourses.val ∧
              PrereqOrder (contents r) prerequisites.val) ∧
        (¬ HasTopoOrder numCourses.val prerequisites.val →
          (contents r).length = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r ∧
        (HasTopoOrder numCourses.val prerequisites.val →
            IsPermOfRange (contents r) numCourses.val ∧
              PrereqOrder (contents r) prerequisites.val) ∧
        (¬ HasTopoOrder numCourses.val prerequisites.val →
          (contents r).length = 0)) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_2 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r) := by
  sorry

/-- The function returns a result r, and either len(r) = 0 or len(r) = numCourses.
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_3 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r ∧
        ((contents r).length = 0 ∨ (contents r).length = numCourses.val.toNat) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r ∧
        ((contents r).length = 0 ∨ (contents r).length = numCourses.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every i with 0 <= i < len(r), 0 <= r[i] < numCourses.
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_4 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ i : Nat, i < (contents r).length →
            ∀ x : Int, (contents r)[i]? = some x → 0 ≤ x ∧ x < numCourses.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ i : Nat, i < (contents r).length →
            ∀ x : Int, (contents r)[i]? = some x → 0 ≤ x ∧ x < numCourses.val) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every i, j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_5 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ i j : Nat, i < j → j < (contents r).length →
            ∀ x y : Int,
              (contents r)[i]? = some x → (contents r)[j]? = some y → x ≠ y := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ i j : Nat, i < j → j < (contents r).length →
            ∀ x y : Int,
              (contents r)[i]? = some x → (contents r)[j]? = some y → x ≠ y) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every c with 0 <= c < numCourses, there exists i with 0 <= i < len(r) such that r[i] = c.
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_6 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ c : Int, 0 ≤ c → c < numCourses.val →
            ∃ i : Nat, i < (contents r).length ∧ (contents r)[i]? = some c := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ c : Int, 0 ≤ c → c < numCourses.val →
            ∃ i : Nat, i < (contents r).length ∧ (contents r)[i]? = some c) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then there exist indices p and q with 0 <= p < len(r), 0 <= q < len(r) such that r[p] = b, r[q] = a, and p < q.
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_7 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] →
            ∃ p q : Nat,
              p < (contents r).length ∧ q < (contents r).length ∧ p < q ∧
                (contents r)[p]? = some b ∧ (contents r)[q]? = some a := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] →
            ∃ p q : Nat,
              p < (contents r).length ∧ q < (contents r).length ∧ p < q ∧
                (contents r)[p]? = some b ∧ (contents r)[q]? = some a) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every i with 0 <= i < len(prerequisites), prerequisites[i][0] != r[0].
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_8 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] →
            (contents r)[0]? ≠ some a := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] →
            (contents r)[0]? ≠ some a) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every i with 0 <= i < len(prerequisites), prerequisites[i][1] != r[len(r)-1].
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_9 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] →
            (contents r)[(contents r).length - 1]? ≠ some b := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ v ∈ prerequisites.val, ∀ a b : Int, contents v = [a, b] →
            (contents r)[(contents r).length - 1]? ≠ some b) := by
  sorry

/-- Whenever the function returns a result r, if there exists a sequence s of length numCourses that is a permutation of {0, 1, ..., numCourses-1} and satisfies: for every j with 0 <= j < len(prerequisites), if prerequisites[j][0] = a and prerequisites[j][1] = b, then the index of b in s is less than the index of a in s; and if for every sequence t of length numCourses that is a permutation of {0, 1, ..., numCourses-1} and satisfies that same ordering property we have t = s, then r = s.
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_10 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        ∀ s : List Int,
          IsPermOfRange s numCourses.val → PrereqOrder s prerequisites.val →
            (∀ t : List Int,
                IsPermOfRange t numCourses.val → PrereqOrder t prerequisites.val →
                  t = s) →
              contents r = s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        ∀ s : List Int,
          IsPermOfRange s numCourses.val → PrereqOrder s prerequisites.val →
            (∀ t : List Int,
                IsPermOfRange t numCourses.val → PrereqOrder t prerequisites.val →
                  t = s) →
              contents r = s) := by
  sorry

/-- Whenever the function returns a result r and r is non-empty, for every i with 0 <= i < len(r) and for every j with 0 <= j < len(prerequisites), if prerequisites[j][0] = r[i], then there exists k with 0 <= k < i such that r[k] = prerequisites[j][1].
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_11 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ i : Nat, i < (contents r).length →
            ∀ j : Nat, j < prerequisites.val.length →
              ∀ v : alloc.vec.Vec Std.I64, prerequisites.val[j]? = some v →
                ∀ a b : Int, contents v = [a, b] →
                  (contents r)[i]? = some a →
                    ∃ k : Nat, k < i ∧ (contents r)[k]? = some b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (contents r).length ≠ 0 →
          ∀ i : Nat, i < (contents r).length →
            ∀ j : Nat, j < prerequisites.val.length →
              ∀ v : alloc.vec.Vec Std.I64, prerequisites.val[j]? = some v →
                ∀ a b : Int, contents v = [a, b] →
                  (contents r)[i]? = some a →
                    ∃ k : Nat, k < i ∧ (contents r)[k]? = some b) := by
  sorry

/-- Whenever the function returns a result r, if there exists a sequence of distinct courses c_0, c_1, ..., c_{k-1} with k >= 1 such that for every i with 0 <= i < k, the pair [c_{(i+1) mod k}, c_i] is in prerequisites (i.e., there exists j with 0 <= j < len(prerequisites) such that prerequisites[j][0] = c_{(i+1) mod k} and prerequisites[j][1] = c_i), then r is empty.
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_12 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (∃ c : List Int, IsCycle prerequisites.val c) → (contents r).length = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r →
        (∃ c : List Int, IsCycle prerequisites.val c) → (contents r).length = 0) := by
  sorry

/-- The function returns a result r, and len(r) = 0 if and only if there does not exist a sequence s of length numCourses that is a permutation of {0, 1, ..., numCourses-1} and satisfies the prerequisite ordering property (for every i with 0 <= i < len(prerequisites), if prerequisites[i][0] = a and prerequisites[i][1] = b, then the index of b in s is less than the index of a in s).
  Preconditions: numCourses is an integer with 1 <= numCourses <= 2000. prerequisites is a slice of vectors, each of length 2. For every i with 0 <= i < len(prerequisites), let a = prerequisites[i][0] and b = prerequisites[i][1]; then 0 <= a, b < numCourses and a != b. All pairs [a, b] are distinct. -/
theorem spec_13 (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r ∧
        ((contents r).length = 0 ↔ ¬ HasTopoOrder numCourses.val prerequisites.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (numCourses : Std.I64) (prerequisites : Slice (alloc.vec.Vec Std.I64))
    (hpre : Preconditions numCourses prerequisites), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindOrder.find_order numCourses prerequisites = ok r ∧
        ((contents r).length = 0 ↔ ¬ HasTopoOrder numCourses.val prerequisites.val)) := by
  sorry

end AegisSpec.FindOrder
