import Aegis.MaxDistToClosest.Code.Funs

/-!
# Specifications of `Aegis.MaxDistToClosest.max_dist_to_closest`

LeetCode problem `maximize-distance-to-closest-person`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxDistToClosest (max_dist_to_closest)

  namespace AegisSpec.MaxDistToClosest

  def seat (seats : Slice Std.I64) (i : ℕ) : ℤ :=
    match seats.val[i]? with
    | some s => s.val
    | none => 0

  def occupied (seats : Slice Std.I64) : Finset ℕ :=
    (Finset.range seats.val.length).filter (fun j => seat seats j = 1)

  def emptySeats (seats : Slice Std.I64) : Finset ℕ :=
    (Finset.range seats.val.length).filter (fun i => seat seats i = 0)

  def distToClosest (seats : Slice Std.I64) (i : ℕ) : ℕ :=
    if h : (occupied seats).Nonempty then
      (occupied seats).inf' h (fun j => Int.natAbs ((i : ℤ) - (j : ℤ)))
    else 0

  def maxDistToClosestValue (seats : Slice Std.I64) : ℕ :=
    if h : (emptySeats seats).Nonempty then
      (emptySeats seats).sup' h (fun i => distToClosest seats i)
    else 0

  def ValidInput (seats : Slice Std.I64) : Prop :=
    2 ≤ seats.val.length ∧ seats.val.length ≤ 20000 ∧
      (∀ i, i < seats.val.length → seat seats i = 0 ∨ seat seats i = 1) ∧
      (∃ i, i < seats.val.length ∧ seat seats i = 1) ∧
      (∃ i, i < seats.val.length ∧ seat seats i = 0)

  /-- Whenever the function returns a result r, r = max { min { |i - j| : 0 <= j < len(seats) and seats[j] = 1 } : 0 <= i < len(seats) and seats[i] = 0 }.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_1 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        r.val = (maxDistToClosestValue seats : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          r.val = (maxDistToClosestValue seats : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail by overflow, out-of-bounds indexing, or panic).
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_2 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∃ r, max_dist_to_closest seats = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∃ r, max_dist_to_closest seats = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(seats) - 1.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_3 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        1 ≤ r.val ∧ r.val ≤ (seats.val.length : ℤ) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          1 ≤ r.val ∧ r.val ≤ (seats.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(seats) and seats[i] = 0, min { |i - j| : 0 <= j < len(seats) and seats[j] = 1 } <= r.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_4 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        ∀ i, i < seats.val.length → seat seats i = 0 →
          (distToClosest seats i : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          ∀ i, i < seats.val.length → seat seats i = 0 →
            (distToClosest seats i : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists i with 0 <= i < len(seats), seats[i] = 0, and min { |i - j| : 0 <= j < len(seats) and seats[j] = 1 } = r.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_5 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        ∃ i, i < seats.val.length ∧ seat seats i = 0 ∧
          (distToClosest seats i : ℤ) = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          ∃ i, i < seats.val.length ∧ seat seats i = 0 ∧
            (distToClosest seats i : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, if seats[0] = 0 and f is the smallest index with 0 <= f < len(seats) and seats[f] = 1, then r >= f.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_6 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r → seat seats 0 = 0 →
        ∀ fst, fst < seats.val.length → seat seats fst = 1 →
          (∀ j, j < fst → seat seats j ≠ 1) → (fst : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r → seat seats 0 = 0 →
          ∀ fst, fst < seats.val.length → seat seats fst = 1 →
            (∀ j, j < fst → seat seats j ≠ 1) → (fst : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if seats[len(seats) - 1] = 0 and l is the largest index with 0 <= l < len(seats) and seats[l] = 1, then r >= len(seats) - 1 - l.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_7 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r → seat seats (seats.val.length - 1) = 0 →
        ∀ lst, lst < seats.val.length → seat seats lst = 1 →
          (∀ j, lst < j → j < seats.val.length → seat seats j ≠ 1) →
            (seats.val.length : ℤ) - 1 - (lst : ℤ) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r → seat seats (seats.val.length - 1) = 0 →
          ∀ lst, lst < seats.val.length → seat seats lst = 1 →
            (∀ j, lst < j → j < seats.val.length → seat seats j ≠ 1) →
              (seats.val.length : ℤ) - 1 - (lst : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices a and b with 0 <= a < b < len(seats), b >= a + 2, seats[a] = 1, seats[b] = 1, and seats[k] = 0 for every k with a < k < b, we have r >= floor((b - a) / 2).
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_8 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        ∀ a b, a < seats.val.length → b < seats.val.length → a + 2 ≤ b →
          seat seats a = 1 → seat seats b = 1 →
            (∀ k, a < k → k < b → seat seats k = 0) →
              (((b - a) / 2 : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          ∀ a b, a < seats.val.length → b < seats.val.length → a + 2 ≤ b →
            seat seats a = 1 → seat seats b = 1 →
              (∀ k, a < k → k < b → seat seats k = 0) →
                (((b - a) / 2 : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = max(p, len(seats) - 1 - p).
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0; there is exactly one index p with seats[p] = 1. -/
  theorem spec_9 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        ∀ p, p < seats.val.length → seat seats p = 1 →
          (∀ q, q < seats.val.length → seat seats q = 1 → q = p) →
            r.val = max (p : ℤ) ((seats.val.length : ℤ) - 1 - (p : ℤ)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          ∀ p, p < seats.val.length → seat seats p = 1 →
            (∀ q, q < seats.val.length → seat seats q = 1 → q = p) →
              r.val = max (p : ℤ) ((seats.val.length : ℤ) - 1 - (p : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r = min { |e - j| : 0 <= j < len(seats) and seats[j] = 1 }.
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0; there is exactly one index e with seats[e] = 0. -/
  theorem spec_10 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        ∀ e, e < seats.val.length → seat seats e = 0 →
          (∀ q, q < seats.val.length → seat seats q = 0 → q = e) →
            r.val = (distToClosest seats e : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          ∀ e, e < seats.val.length → seat seats e = 0 →
            (∀ q, q < seats.val.length → seat seats q = 0 → q = e) →
              r.val = (distToClosest seats e : ℤ)) := by
    sorry

  /-- If the function returns r on seats and r2 on seats2, then r2 <= r.
    Preconditions: seats and seats2 have the same length len, with 2 <= len <= 20000; both satisfy the valid-input constraints (entries are 0 or 1, at least one 1, at least one 0); for every i with 0 <= i < len, seats[i] <= seats2[i]. -/
  theorem spec_11 (seats seats2 : Slice Std.I64) (h1 : ValidInput seats)
      (h2 : ValidInput seats2) (hlen : seats.val.length = seats2.val.length)
      (hle : ∀ i, i < seats.val.length → seat seats i ≤ seat seats2 i) :
      ∀ r r2, max_dist_to_closest seats = ok r → max_dist_to_closest seats2 = ok r2 →
        r2.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (seats seats2 : Slice Std.I64) (h1 : ValidInput seats)
        (h2 : ValidInput seats2) (hlen : seats.val.length = seats2.val.length)
        (hle : ∀ i, i < seats.val.length → seat seats i ≤ seat seats2 i), ∀ r r2, max_dist_to_closest seats = ok r → max_dist_to_closest seats2 = ok r2 →
          r2.val ≤ r.val) := by
    sorry

  /-- If the function returns r on seats and r_rev on rev, then r = r_rev.
    Preconditions: seats satisfies the valid-input constraints: len(seats) is between 2 and 20000 inclusive, every seat is 0 or 1, at least one seat is 1, and at least one seat is 0; rev is the same-length array defined by rev[i] = seats[len(seats) - 1 - i] for every 0 <= i < len(seats). -/
  theorem spec_12 (seats rev : Slice Std.I64) (h : ValidInput seats)
      (hlen : rev.val.length = seats.val.length)
      (hrev : ∀ i, i < seats.val.length →
        seat rev i = seat seats (seats.val.length - 1 - i)) :
      ∀ r rrev, max_dist_to_closest seats = ok r → max_dist_to_closest rev = ok rrev →
        r.val = rrev.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (seats rev : Slice Std.I64) (h : ValidInput seats)
        (hlen : rev.val.length = seats.val.length)
        (hrev : ∀ i, i < seats.val.length →
          seat rev i = seat seats (seats.val.length - 1 - i)), ∀ r rrev, max_dist_to_closest seats = ok r → max_dist_to_closest rev = ok rrev →
          r.val = rrev.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every i with 0 <= i < len(seats) and seats[i] = 0, at least one of the following holds: (i > 0 and seats[i - 1] = 1) or (i + 1 < len(seats) and seats[i + 1] = 1).
    Preconditions: len(seats) is between 2 and 20000 inclusive; for every i with 0 <= i < len(seats), seats[i] is either 0 or 1; there is at least one i with seats[i] = 1; there is at least one i with seats[i] = 0. -/
  theorem spec_13 (seats : Slice Std.I64) (h : ValidInput seats) :
      ∀ r, max_dist_to_closest seats = ok r →
        (r.val = 1 ↔
          ∀ i, i < seats.val.length → seat seats i = 0 →
            (0 < i ∧ seat seats (i - 1) = 1) ∨
              (i + 1 < seats.val.length ∧ seat seats (i + 1) = 1)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (seats : Slice Std.I64) (h : ValidInput seats), ∀ r, max_dist_to_closest seats = ok r →
          (r.val = 1 ↔
            ∀ i, i < seats.val.length → seat seats i = 0 →
              (0 < i ∧ seat seats (i - 1) = 1) ∨
                (i + 1 < seats.val.length ∧ seat seats (i + 1) = 1))) := by
    sorry

  end AegisSpec.MaxDistToClosest
