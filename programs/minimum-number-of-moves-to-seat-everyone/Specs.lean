import Aegis.MinMovesToSeat.Code.Funs

/-!
# Specifications of `Aegis.MinMovesToSeat.min_moves_to_seat`

LeetCode problem `minimum-number-of-moves-to-seat-everyone`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinMovesToSeat

namespace AegisSpec.MinMovesToSeat

def nthElem {α : Type} (l : List α) (n : Nat) (h : l.length = n) (i : Fin n) : α :=
  l.get (Fin.cast h.symm i)

def sliceVals (s : Slice Std.I64) (n : Nat) (h : s.val.length = n) : Fin n → ℤ :=
  fun i => (nthElem s.val n h i).val

def permCost {n : Nat} (seats students : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℤ :=
  ∑ j : Fin n, |students j - seats (σ j)|

def IsMinCost {n : Nat} (seats students : Fin n → ℤ) (v : ℤ) : Prop :=
  IsLeast {w : ℤ | ∃ σ : Equiv.Perm (Fin n), permCost seats students σ = w} v

def BoundedIn (lo hi : ℤ) (l : List Std.I64) : Prop :=
  ∀ (i : Nat) (h : i < l.length), lo ≤ (l.get ⟨i, h⟩).val ∧ (l.get ⟨i, h⟩).val ≤ hi

def Nondecreasing (l : List ℤ) : Prop := l.Pairwise (· ≤ ·)

def IsSortedRearrangement (s : Slice Std.I64) (n : Nat) (a : List ℤ) : Prop :=
  a.length = n ∧ Nondecreasing a ∧ a.Perm (s.val.map fun x => x.val)

def IsPermutedCopy (src dst : Slice Std.I64) (n : Nat)
    (hsrc : src.val.length = n) (hdst : dst.val.length = n)
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, sliceVals dst n hdst i = sliceVals src n hsrc (p i)

def IsShiftedBy (src dst : Slice Std.I64) (n : Nat)
    (hsrc : src.val.length = n) (hdst : dst.val.length = n) (c : ℤ) : Prop :=
  (∀ i : Fin n, 1 ≤ sliceVals src n hsrc i + c ∧ sliceVals src n hsrc i + c ≤ 100) ∧
  (∀ i : Fin n, sliceVals dst n hdst i = sliceVals src n hsrc i + c)

def IsScaledBy (src dst : Slice Std.I64) (n : Nat)
    (hsrc : src.val.length = n) (hdst : dst.val.length = n) (k : ℤ) : Prop :=
  0 < k ∧
  (∀ i : Fin n, 1 ≤ k * sliceVals src n hsrc i ∧ k * sliceVals src n hsrc i ≤ 100) ∧
  (∀ i : Fin n, sliceVals dst n hdst i = k * sliceVals src n hsrc i)

/-- Whenever the function returns a result r, r (viewed as an integer) equals the minimum, over all bijections sigma from {0,...,n-1} to {0,...,n-1}, of sum_{j=0}^{n-1} abs(students[j] - seats[sigma(j)]).
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_1 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r) :
    IsMinCost (sliceVals seats n hseats) (sliceVals students n hstudents) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r), IsMinCost (sliceVals seats n hseats) (sliceVals students n hstudents) r.val) := by
  sorry

/-- The function returns a result r (it does not fail by overflow, out-of-bounds access, or panic) for every pair of slices satisfying the preconditions.
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_2 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val) :
    ∃ r : Std.I64, min_moves_to_seat seats students = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val), ∃ r : Std.I64, min_moves_to_seat seats students = ok r) := by
  sorry

/-- Whenever the function returns a result r, let a be a list of length n obtained by rearranging the multiset {seats[0],...,seats[n-1]} in nondecreasing order, and let b be a list of length n obtained by rearranging the multiset {students[0],...,students[n-1]} in nondecreasing order. Then r = sum_{i=0}^{n-1} abs(b[i] - a[i]).
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_3 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (a b : List ℤ)
    (ha : IsSortedRearrangement seats n a) (hb : IsSortedRearrangement students n b)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r) :
    r.val = ∑ i : Fin n,
      |nthElem b n hb.1 i - nthElem a n ha.1 i| := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (a b : List ℤ)
    (ha : IsSortedRearrangement seats n a) (hb : IsSortedRearrangement students n b)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r), r.val = ∑ i : Fin n,
      |nthElem b n hb.1 i - nthElem a n ha.1 i|) := by
  sorry

/-- Whenever the function returns a result r, r >= abs((sum_{j=0}^{n-1} students[j]) - (sum_{i=0}^{n-1} seats[i])).
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_4 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r) :
    |(∑ j : Fin n, sliceVals students n hstudents j) -
      (∑ i : Fin n, sliceVals seats n hseats i)| ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r), |(∑ j : Fin n, sliceVals students n hstudents j) -
      (∑ i : Fin n, sliceVals seats n hseats i)| ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{j=0}^{n-1} abs(students[j] - seats[j]).
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_5 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r) :
    r.val ≤ ∑ j : Fin n, |sliceVals students n hstudents j - sliceVals seats n hseats j| := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r), r.val ≤ ∑ j : Fin n, |sliceVals students n hstudents j - sliceVals seats n hseats j|) := by
  sorry

/-- Whenever the function returns a result r, r and (sum_{j=0}^{n-1} students[j] - sum_{i=0}^{n-1} seats[i]) have the same parity; equivalently, they are congruent modulo 2.
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_6 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r) :
    Int.ModEq 2 r.val
      ((∑ j : Fin n, sliceVals students n hstudents j) -
        (∑ i : Fin n, sliceVals seats n hseats i)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r), Int.ModEq 2 r.val
      ((∑ j : Fin n, sliceVals students n hstudents j) -
        (∑ i : Fin n, sliceVals seats n hseats i))) := by
  sorry

/-- For any bijections p and q from {0,...,n-1} to {0,...,n-1}, let seats' be the slice defined by seats'[i] = seats[p(i)] and students' be the slice defined by students'[j] = students[q(j)]. Whenever the function returns r on (seats, students) and returns r' on (seats', students'), we have r = r'.
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_7 (seats students seats' students' : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hseats' : seats'.val.length = n) (hstudents' : students'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (p q : Equiv.Perm (Fin n))
    (hp : IsPermutedCopy seats seats' n hseats hseats' p)
    (hq : IsPermutedCopy students students' n hstudents hstudents' q)
    (r r' : Std.I64)
    (hr : min_moves_to_seat seats students = ok r)
    (hr' : min_moves_to_seat seats' students' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (seats students seats' students' : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hseats' : seats'.val.length = n) (hstudents' : students'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (p q : Equiv.Perm (Fin n))
    (hp : IsPermutedCopy seats seats' n hseats hseats' p)
    (hq : IsPermutedCopy students students' n hstudents hstudents' q)
    (r r' : Std.I64)
    (hr : min_moves_to_seat seats students = ok r)
    (hr' : min_moves_to_seat seats' students' = ok r'), r.val = r'.val) := by
  sorry

/-- For every integer c such that 1 <= seats[i]+c <= 100 for every 0 <= i < n and 1 <= students[j]+c <= 100 for every 0 <= j < n, let seats'[i] = seats[i]+c and students'[j] = students[j]+c. Whenever the function returns r on (seats, students) and returns r' on (seats', students'), we have r = r'.
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_8 (seats students seats' students' : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hseats' : seats'.val.length = n) (hstudents' : students'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (c : ℤ)
    (hc : IsShiftedBy seats seats' n hseats hseats' c)
    (hc' : IsShiftedBy students students' n hstudents hstudents' c)
    (r r' : Std.I64)
    (hr : min_moves_to_seat seats students = ok r)
    (hr' : min_moves_to_seat seats' students' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (seats students seats' students' : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hseats' : seats'.val.length = n) (hstudents' : students'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (c : ℤ)
    (hc : IsShiftedBy seats seats' n hseats hseats' c)
    (hc' : IsShiftedBy students students' n hstudents hstudents' c)
    (r r' : Std.I64)
    (hr : min_moves_to_seat seats students = ok r)
    (hr' : min_moves_to_seat seats' students' = ok r'), r.val = r'.val) := by
  sorry

/-- For every positive integer k such that 1 <= k*seats[i] <= 100 for every 0 <= i < n and 1 <= k*students[j] <= 100 for every 0 <= j < n, let seats'[i] = k*seats[i] and students'[j] = k*students[j]. Whenever the function returns r on (seats, students) and returns r' on (seats', students'), we have r' = k*r.
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_9 (seats students seats' students' : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hseats' : seats'.val.length = n) (hstudents' : students'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (k : ℤ)
    (hk : IsScaledBy seats seats' n hseats hseats' k)
    (hk' : IsScaledBy students students' n hstudents hstudents' k)
    (r r' : Std.I64)
    (hr : min_moves_to_seat seats students = ok r)
    (hr' : min_moves_to_seat seats' students' = ok r') :
    r'.val = k * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (seats students seats' students' : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hseats' : seats'.val.length = n) (hstudents' : students'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (k : ℤ)
    (hk : IsScaledBy seats seats' n hseats hseats' k)
    (hk' : IsScaledBy students students' n hstudents hstudents' k)
    (r r' : Std.I64)
    (hr : min_moves_to_seat seats students = ok r)
    (hr' : min_moves_to_seat seats' students' = ok r'), r'.val = k * r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a bijection sigma from {0,...,n-1} to {0,...,n-1} such that sum_{j=0}^{n-1} abs(students[j] - seats[sigma(j)]) = r.
  Preconditions: n = len(seats) = len(students), 1 <= n <= 100, for every i with 0 <= i < n we have 1 <= seats[i] <= 100, and for every j with 0 <= j < n we have 1 <= students[j] <= 100. -/
theorem spec_10 (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r) :
    ∃ σ : Equiv.Perm (Fin n),
      permCost (sliceVals seats n hseats) (sliceVals students n hstudents) σ = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (seats students : Slice Std.I64) (n : Nat)
    (hseats : seats.val.length = n) (hstudents : students.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbseats : BoundedIn 1 100 seats.val) (hbstudents : BoundedIn 1 100 students.val)
    (r : Std.I64) (hr : min_moves_to_seat seats students = ok r), ∃ σ : Equiv.Perm (Fin n),
      permCost (sliceVals seats n hseats) (sliceVals students n hstudents) σ = r.val) := by
  sorry

end AegisSpec.MinMovesToSeat
