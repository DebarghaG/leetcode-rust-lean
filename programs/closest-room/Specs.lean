import Aegis.ClosestRoom.Code.Funs

/-!
# Specifications of `Aegis.ClosestRoom.closest_room`

LeetCode problem `closest-room`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ClosestRoom

def rowGet (rows : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match rows.val[i]? with
  | none => 0
  | some v => ((v.val[j]?).map (fun x => x.val)).getD 0

def rowLen (rows : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  match rows.val[i]? with
  | none => 0
  | some v => v.val.length

def roomId (rooms : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := rowGet rooms i 0

def roomSize (rooms : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := rowGet rooms i 1

def queryId (queries : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int := rowGet queries j 0

def querySize (queries : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Int := rowGet queries j 1

def ans (r : alloc.vec.Vec Std.I64) (j : Nat) : Int :=
  ((r.val[j]?).map (fun x => x.val)).getD (-1)

def IsRoomId (rooms : Slice (alloc.vec.Vec Std.I64)) (id : Int) : Prop :=
  ∃ i, i < rooms.val.length ∧ roomId rooms i = id

def NoAdmissible (rooms : Slice (alloc.vec.Vec Std.I64)) (m : Int) : Prop :=
  ∀ i, i < rooms.val.length → ¬ (roomSize rooms i ≥ m)

def SomeAdmissible (rooms : Slice (alloc.vec.Vec Std.I64)) (m : Int) : Prop :=
  ∃ i, i < rooms.val.length ∧ roomSize rooms i ≥ m

def RoomsWellFormed (rooms : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (1 ≤ rooms.val.length ∧ rooms.val.length ≤ 100000) ∧
  (∀ i, i < rooms.val.length →
    rowLen rooms i = 2 ∧
      1 ≤ roomId rooms i ∧ roomId rooms i ≤ 10000000 ∧
      1 ≤ roomSize rooms i ∧ roomSize rooms i ≤ 10000000) ∧
  (∀ i l, i < l → l < rooms.val.length → roomId rooms i ≠ roomId rooms l)

def QueriesWellFormed (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (1 ≤ queries.val.length ∧ queries.val.length ≤ 10000) ∧
  (∀ j, j < queries.val.length →
    rowLen queries j = 2 ∧
      1 ≤ queryId queries j ∧ queryId queries j ≤ 10000000 ∧
      1 ≤ querySize queries j ∧ querySize queries j ≤ 10000000)

def WellFormed (rooms queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  RoomsWellFormed rooms ∧ QueriesWellFormed queries

/-- The function returns a result r such that len(r) = len(queries), and for every j with 0 <= j < len(queries), writing p = queries[j][0] and m = queries[j][1]: if there is no i with 0 <= i < len(rooms) and rooms[i][1] >= m, then r[j] = -1; otherwise r[j] is a room id (there is exactly one i with rooms[i][0] = r[j]), that room satisfies rooms[i][1] >= m, and for every i with 0 <= i < len(rooms) and rooms[i][1] >= m, either abs(r[j] - p) < abs(rooms[i][0] - p), or abs(r[j] - p) = abs(rooms[i][0] - p) and r[j] <= rooms[i][0].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_1 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ j, j < queries.val.length →
        (NoAdmissible rooms (querySize queries j) → ans r j = -1) ∧
        (SomeAdmissible rooms (querySize queries j) →
          IsRoomId rooms (ans r j) ∧
          (∀ i l, i < rooms.val.length → l < rooms.val.length →
            roomId rooms i = ans r j → roomId rooms l = ans r j → i = l) ∧
          (∃ i, i < rooms.val.length ∧ roomId rooms i = ans r j ∧
            roomSize rooms i ≥ querySize queries j) ∧
          (∀ i, i < rooms.val.length → roomSize rooms i ≥ querySize queries j →
            |ans r j - queryId queries j| < |roomId rooms i - queryId queries j| ∨
            (|ans r j - queryId queries j| = |roomId rooms i - queryId queries j| ∧
              ans r j ≤ roomId rooms i))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ j, j < queries.val.length →
        (NoAdmissible rooms (querySize queries j) → ans r j = -1) ∧
        (SomeAdmissible rooms (querySize queries j) →
          IsRoomId rooms (ans r j) ∧
          (∀ i l, i < rooms.val.length → l < rooms.val.length →
            roomId rooms i = ans r j → roomId rooms l = ans r j → i = l) ∧
          (∃ i, i < rooms.val.length ∧ roomId rooms i = ans r j ∧
            roomSize rooms i ≥ querySize queries j) ∧
          (∀ i, i < rooms.val.length → roomSize rooms i ≥ querySize queries j →
            |ans r j - queryId queries j| < |roomId rooms i - queryId queries j| ∨
            (|ans r j - queryId queries j| = |roomId rooms i - queryId queries j| ∧
              ans r j ≤ roomId rooms i)))) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(queries).
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_2 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r → r.val.length = queries.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r → r.val.length = queries.val.length) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_3 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.ClosestRoom.closest_room rooms queries = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∃ r : alloc.vec.Vec Std.I64, Aegis.ClosestRoom.closest_room rooms queries = ok r) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries), either r[j] = -1 or 1 <= r[j] <= 10000000.
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_4 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j = -1 ∨ (1 ≤ ans r j ∧ ans r j ≤ 10000000) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j = -1 ∨ (1 ≤ ans r j ∧ ans r j ≤ 10000000)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries), either r[j] = -1, or there exists i with 0 <= i < len(rooms) such that rooms[i][0] = r[j].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_5 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j = -1 ∨ IsRoomId rooms (ans r j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j = -1 ∨ IsRoomId rooms (ans r j)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries), if r[j] != -1 then there exists i with 0 <= i < len(rooms) such that rooms[i][0] = r[j] and rooms[i][1] >= queries[j][1].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_6 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j ≠ -1 →
        ∃ i, i < rooms.val.length ∧ roomId rooms i = ans r j ∧
          roomSize rooms i ≥ querySize queries j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j ≠ -1 →
        ∃ i, i < rooms.val.length ∧ roomId rooms i = ans r j ∧
          roomSize rooms i ≥ querySize queries j) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries), r[j] = -1 if and only if there is no i with 0 <= i < len(rooms) and rooms[i][1] >= queries[j][1].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_7 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length →
        (ans r j = -1 ↔ NoAdmissible rooms (querySize queries j)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length →
        (ans r j = -1 ↔ NoAdmissible rooms (querySize queries j))) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries) and r[j] != -1, and for every i with 0 <= i < len(rooms) and rooms[i][1] >= queries[j][1], abs(r[j] - queries[j][0]) <= abs(rooms[i][0] - queries[j][0]).
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_8 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j ≠ -1 →
        ∀ i, i < rooms.val.length → roomSize rooms i ≥ querySize queries j →
          |ans r j - queryId queries j| ≤ |roomId rooms i - queryId queries j| := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j ≠ -1 →
        ∀ i, i < rooms.val.length → roomSize rooms i ≥ querySize queries j →
          |ans r j - queryId queries j| ≤ |roomId rooms i - queryId queries j|) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries) and r[j] != -1, and for every i with 0 <= i < len(rooms) and rooms[i][1] >= queries[j][1], if abs(r[j] - queries[j][0]) = abs(rooms[i][0] - queries[j][0]), then r[j] <= rooms[i][0].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_9 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j ≠ -1 →
        ∀ i, i < rooms.val.length → roomSize rooms i ≥ querySize queries j →
          |ans r j - queryId queries j| = |roomId rooms i - queryId queries j| →
            ans r j ≤ roomId rooms i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → ans r j ≠ -1 →
        ∀ i, i < rooms.val.length → roomSize rooms i ≥ querySize queries j →
          |ans r j - queryId queries j| = |roomId rooms i - queryId queries j| →
            ans r j ≤ roomId rooms i) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries), if there exists i with 0 <= i < len(rooms) such that rooms[i][0] = queries[j][0] and rooms[i][1] >= queries[j][1], then r[j] = queries[j][0].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_10 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length →
        (∃ i, i < rooms.val.length ∧ roomId rooms i = queryId queries j ∧
          roomSize rooms i ≥ querySize queries j) →
          ans r j = queryId queries j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length →
        (∃ i, i < rooms.val.length ∧ roomId rooms i = queryId queries j ∧
          roomSize rooms i ≥ querySize queries j) →
          ans r j = queryId queries j) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries), if there is exactly one i with 0 <= i < len(rooms) and rooms[i][1] >= queries[j][1], then r[j] = rooms[i][0] for that unique i.
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_11 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length →
        (∃ i, i < rooms.val.length ∧ roomSize rooms i ≥ querySize queries j ∧
          ∀ l, l < rooms.val.length → roomSize rooms l ≥ querySize queries j → l = i) →
          ∃ i, i < rooms.val.length ∧ roomSize rooms i ≥ querySize queries j ∧
            ans r j = roomId rooms i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length →
        (∃ i, i < rooms.val.length ∧ roomSize rooms i ≥ querySize queries j ∧
          ∀ l, l < rooms.val.length → roomSize rooms l ≥ querySize queries j → l = i) →
          ∃ i, i < rooms.val.length ∧ roomSize rooms i ≥ querySize queries j ∧
            ans r j = roomId rooms i) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j with 0 <= j < len(queries) and queries[j][1] = 1, r[j] is not -1 and r[j] is the room id minimizing abs(id - queries[j][0]) over all room ids id in rooms, with the smallest such id used when a tie occurs.
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_12 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → querySize queries j = 1 →
        ans r j ≠ -1 ∧
        IsRoomId rooms (ans r j) ∧
        (∀ i, i < rooms.val.length →
          |ans r j - queryId queries j| < |roomId rooms i - queryId queries j| ∨
          (|ans r j - queryId queries j| = |roomId rooms i - queryId queries j| ∧
            ans r j ≤ roomId rooms i)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j, j < queries.val.length → querySize queries j = 1 →
        ans r j ≠ -1 ∧
        IsRoomId rooms (ans r j) ∧
        (∀ i, i < rooms.val.length →
          |ans r j - queryId queries j| < |roomId rooms i - queryId queries j| ∨
          (|ans r j - queryId queries j| = |roomId rooms i - queryId queries j| ∧
            ans r j ≤ roomId rooms i))) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), if len(rooms) = 1 then for every j with 0 <= j < len(queries), r[j] = rooms[0][0] when rooms[0][1] >= queries[j][1], and r[j] = -1 otherwise.
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_13 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      rooms.val.length = 1 →
      ∀ j, j < queries.val.length →
        (roomSize rooms 0 ≥ querySize queries j → ans r j = roomId rooms 0) ∧
        (¬ (roomSize rooms 0 ≥ querySize queries j) → ans r j = -1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      rooms.val.length = 1 →
      ∀ j, j < queries.val.length →
        (roomSize rooms 0 ≥ querySize queries j → ans r j = roomId rooms 0) ∧
        (¬ (roomSize rooms 0 ≥ querySize queries j) → ans r j = -1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j and l with 0 <= j < len(queries) and 0 <= l < len(queries), if queries[j][0] = queries[l][0] and queries[j][1] = queries[l][1], then r[j] = r[l].
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_14 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j l, j < queries.val.length → l < queries.val.length →
        queryId queries j = queryId queries l →
        querySize queries j = querySize queries l → ans r j = ans r l := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j l, j < queries.val.length → l < queries.val.length →
        queryId queries j = queryId queries l →
        querySize queries j = querySize queries l → ans r j = ans r l) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(queries), for every j and l with 0 <= j < len(queries) and 0 <= l < len(queries), if queries[j][0] = queries[l][0], queries[j][1] <= queries[l][1], and r[l] != -1, then r[j] != -1 and abs(r[j] - queries[j][0]) <= abs(r[l] - queries[j][0]).
  Preconditions: len(rooms) is between 1 and 100000 inclusive; len(queries) is between 1 and 10000 inclusive; for every i with 0 <= i < len(rooms), len(rooms[i]) = 2, 1 <= rooms[i][0] <= 10000000, and 1 <= rooms[i][1] <= 10000000; for every i and l with 0 <= i < l < len(rooms), rooms[i][0] != rooms[l][0]; for every j with 0 <= j < len(queries), len(queries[j]) = 2, 1 <= queries[j][0] <= 10000000, and 1 <= queries[j][1] <= 10000000. -/
theorem spec_15 (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j l, j < queries.val.length → l < queries.val.length →
        queryId queries j = queryId queries l →
        querySize queries j ≤ querySize queries l →
        ans r l ≠ -1 →
          ans r j ≠ -1 ∧
          |ans r j - queryId queries j| ≤ |ans r l - queryId queries j| := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (rooms queries : Slice (alloc.vec.Vec Std.I64))
    (h : WellFormed rooms queries), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.ClosestRoom.closest_room rooms queries = ok r →
      r.val.length = queries.val.length →
      ∀ j l, j < queries.val.length → l < queries.val.length →
        queryId queries j = queryId queries l →
        querySize queries j ≤ querySize queries l →
        ans r l ≠ -1 →
          ans r j ≠ -1 ∧
          |ans r j - queryId queries j| ≤ |ans r l - queryId queries j|) := by
  sorry

end AegisSpec.ClosestRoom
