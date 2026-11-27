import Aegis.MostPoints.Code.Funs

/-!
# Specifications of `Aegis.MostPoints.most_points`

LeetCode problem `solving-questions-with-brainpower`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MostPoints (most_points)

namespace AegisSpec.MostPoints

open Classical

def rows (questions : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  questions.list.toList.map (fun v => v.slice.list.toList.map (fun x => x.val))

def size (questions : Slice (alloc.vec.Vec Std.I64)) : Nat := (Slice.len questions).val

def entry (questions : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match (rows questions)[i]? with
  | some row => (row[j]?).getD 0
  | none => 0

def points (questions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  entry questions i 0

def brain (questions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  entry questions i 1

def ShapeOk (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  n = size questions ∧
    ∀ i, i < n → ∃ row, (rows questions)[i]? = some row ∧ row.length = 2

def BoundsOk (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  (∀ i, i < n → 1 ≤ points questions i ∧ points questions i ≤ 100000) ∧
    ∀ i, i < n → 0 ≤ brain questions i ∧ brain questions i ≤ 100000

def Admissible (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (S : Finset Nat) : Prop :=
  S ⊆ Finset.range n ∧
    ∀ i ∈ S, ∀ j ∈ S, i < j → (j : Int) > (i : Int) + brain questions i

def total (questions : Slice (alloc.vec.Vec Std.I64)) (S : Finset Nat) : Int :=
  ∑ i ∈ S, points questions i

lemma admissible_empty (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat) :
    ∅ ∈ (Finset.range n).powerset.filter (Admissible questions n) := by
  simp [Admissible]

noncomputable def best (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Int :=
  Finset.sup' ((Finset.range n).powerset.filter (Admissible questions n))
    ⟨∅, admissible_empty questions n⟩ (total questions)

def maxPoints (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Int :=
  ((List.range n).map (points questions)).max?.getD 0

def ceilHalf (n : Nat) : Int := (((n + 1) / 2 : Nat) : Int)

/-- Whenever the function returns a result r, r is the maximum, over all sets S subset of {0,...,n-1} such that for every i,j in S with i < j we have j > i + b_i, of the sum of p_i over i in S. The empty set is allowed and has sum 0. Equivalently, r is the maximum total points obtainable by choosing solved questions in order, where solving i forbids solving any j with i < j <= i + b_i.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_1 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    r.val = best questions n := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), r.val = best questions n) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail: no overflow, out-of-bounds access, panic, or other failure).
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_2 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n) :
    ∃ r : Std.I64, most_points questions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n), ∃ r : Std.I64, most_points questions = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r >= p_i.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_3 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    ∀ i, i < n → points questions i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), ∀ i, i < n → points questions i ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} p_i.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_4 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    r.val ≤ ∑ i ∈ Finset.range n, points questions i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), r.val ≤ ∑ i ∈ Finset.range n, points questions i) := by
  sorry

/-- Whenever the function returns a result r, if n = 1 then r = p_0.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_5 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    n = 1 → r.val = points questions 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), n = 1 → r.val = points questions 0) := by
  sorry

/-- Whenever the function returns a result r, if n = 2 then r = p_0 + p_1 if b_0 = 0, and r = max(p_0, p_1) otherwise.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_6 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    n = 2 →
      (brain questions 0 = 0 → r.val = points questions 0 + points questions 1) ∧
      (brain questions 0 ≠ 0 →
        r.val = max (points questions 0) (points questions 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), n = 2 →
      (brain questions 0 = 0 → r.val = points questions 0 + points questions 1) ∧
      (brain questions 0 ≠ 0 →
        r.val = max (points questions 0) (points questions 1))) := by
  sorry

/-- Whenever the function returns a result r, if b_i = 0 for every i with 0 <= i < n, then r = sum_{i=0}^{n-1} p_i.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_7 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    (∀ i, i < n → brain questions i = 0) →
      r.val = ∑ i ∈ Finset.range n, points questions i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), (∀ i, i < n → brain questions i = 0) →
      r.val = ∑ i ∈ Finset.range n, points questions i) := by
  sorry

/-- Whenever the function returns a result r, if b_i >= n - 1 for every i with 0 <= i < n, then r = max_{0 <= i < n} p_i.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_8 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    (∀ i, i < n → (n : Int) - 1 ≤ brain questions i) →
      r.val = maxPoints questions n := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), (∀ i, i < n → (n : Int) - 1 ≤ brain questions i) →
      r.val = maxPoints questions n) := by
  sorry

/-- Whenever most_points(questions) returns r and most_points(questions') returns r', we have r = r'.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. Let questions' be another input satisfying the same shape and bounds, with len(questions') = n, and let p'_i = questions'[i][0] and b'_i = questions'[i][1]. Assume that for every i with 0 <= i < n-1, p'_i = p_i and b'_i = b_i, and that p'_{n-1} = p_{n-1}, while b'_{n-1} is any integer with 0 <= b'_{n-1} <= 100000. -/
theorem spec_9 (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' n) (hbounds' : BoundsOk questions' n)
    (hkeep : ∀ i, i < n - 1 →
      points questions' i = points questions i ∧ brain questions' i = brain questions i)
    (hlast : points questions' (n - 1) = points questions (n - 1))
    (hb_last : 0 ≤ brain questions' (n - 1) ∧ brain questions' (n - 1) ≤ 100000)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' n) (hbounds' : BoundsOk questions' n)
    (hkeep : ∀ i, i < n - 1 →
      points questions' i = points questions i ∧ brain questions' i = brain questions i)
    (hlast : points questions' (n - 1) = points questions (n - 1))
    (hb_last : 0 ≤ brain questions' (n - 1) ∧ brain questions' (n - 1) ≤ 100000)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever most_points(questions) returns r and most_points(questions') returns r', we have r <= r'.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. Let questions' be another input satisfying the same shape and bounds, with len(questions') = n, and let p'_i = questions'[i][0] and b'_i = questions'[i][1]. Assume that for every i with 0 <= i < n, b'_i = b_i and p_i <= p'_i. -/
theorem spec_10 (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' n) (hbounds' : BoundsOk questions' n)
    (hb : ∀ i, i < n → brain questions' i = brain questions i)
    (hp : ∀ i, i < n → points questions i ≤ points questions' i)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' n) (hbounds' : BoundsOk questions' n)
    (hb : ∀ i, i < n → brain questions' i = brain questions i)
    (hp : ∀ i, i < n → points questions i ≤ points questions' i)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever most_points(questions) returns r and most_points(questions') returns r', we have r >= r'.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. Let questions' be another input satisfying the same shape and bounds, with len(questions') = n, and let p'_i = questions'[i][0] and b'_i = questions'[i][1]. Assume that for every i with 0 <= i < n, p'_i = p_i and b_i <= b'_i. -/
theorem spec_11 (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' n) (hbounds' : BoundsOk questions' n)
    (hp : ∀ i, i < n → points questions' i = points questions i)
    (hb : ∀ i, i < n → brain questions i ≤ brain questions' i)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' n) (hbounds' : BoundsOk questions' n)
    (hp : ∀ i, i < n → points questions' i = points questions i)
    (hb : ∀ i, i < n → brain questions i ≤ brain questions' i)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r'), r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a set S subset of {0,...,n-1} such that for every i,j in S with i < j we have j > i + b_i, and sum_{i in S} p_i = r.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_12 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r) :
    ∃ S : Finset Nat, Admissible questions n S ∧ total questions S = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (r : Std.I64) (hr : most_points questions = ok r), ∃ S : Finset Nat, Admissible questions n S ∧ total questions S = r.val) := by
  sorry

/-- Whenever the function returns a result r, if p_i = c for every i with 0 <= i < n and b_i = 1 for every i with 0 <= i < n, then r = c * ceil(n/2), where ceil(n/2) is the least integer m with m >= n/2 (equivalently, c * ((n+1) div 2) using integer division).
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. -/
theorem spec_13 (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (c : Int) (r : Std.I64) (hr : most_points questions = ok r) :
    (∀ i, i < n → points questions i = c) →
    (∀ i, i < n → brain questions i = 1) → r.val = c * ceilHalf n := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (questions : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hshape : ShapeOk questions n)
    (hbounds : BoundsOk questions n)
    (c : Int) (r : Std.I64) (hr : most_points questions = ok r), (∀ i, i < n → points questions i = c) →
    (∀ i, i < n → brain questions i = 1) → r.val = c * ceilHalf n) := by
  sorry

/-- Whenever most_points(questions) returns r and most_points(questions') returns r', we have r' >= r.
  Preconditions: Let n = len(questions). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(questions[i]) = 2. Let p_i = questions[i][0] and b_i = questions[i][1]. Assume 1 <= p_i <= 100000 and 0 <= b_i <= 100000 for every i with 0 <= i < n. Assume n < 100000. Let questions' be another valid input with len(questions') = n+1, questions'[i] = questions[i] for every 0 <= i < n, and for the appended index n let p'_n = questions'[n][0] and b'_n = questions'[n][1] satisfy 1 <= p'_n <= 100000 and 0 <= b'_n <= 100000. -/
theorem spec_14 (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hn3 : n < 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' (n + 1)) (hbounds' : BoundsOk questions' (n + 1))
    (hkeep : ∀ i, i < n →
      points questions' i = points questions i ∧ brain questions' i = brain questions i)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (questions questions' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000) (hn3 : n < 100000)
    (hshape : ShapeOk questions n) (hbounds : BoundsOk questions n)
    (hshape' : ShapeOk questions' (n + 1)) (hbounds' : BoundsOk questions' (n + 1))
    (hkeep : ∀ i, i < n →
      points questions' i = points questions i ∧ brain questions' i = brain questions i)
    (r r' : Std.I64) (hr : most_points questions = ok r)
    (hr' : most_points questions' = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MostPoints
