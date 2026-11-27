import Aegis.CanVisitAllRooms.Code.Funs

/-!
# Specifications of `Aegis.CanVisitAllRooms.can_visit_all_rooms`

LeetCode problem `keys-and-rooms`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanVisitAllRooms

open Aegis.CanVisitAllRooms (can_visit_all_rooms)

abbrev Rooms := Slice (alloc.vec.Vec Std.I64)

def numRooms (rooms : Rooms) : ℕ := (Slice.len rooms).val

def roomKeys (rooms : Rooms) (i : ℕ) : List ℤ :=
  match rooms.val[i]? with
  | some row => row.val.map (fun k => k.val)
  | none => []

def allRoomKeys (rooms : Rooms) : List (List ℤ) :=
  rooms.val.map (fun row => row.val.map (fun k => k.val))

def totalKeys (rooms : Rooms) : ℕ := (allRoomKeys rooms).map List.length |>.sum

def LenBounds (rooms : Rooms) : Prop :=
  2 ≤ numRooms rooms ∧ numRooms rooms ≤ 1000

def RowLenBounds (rooms : Rooms) : Prop :=
  ∀ i : ℕ, i < numRooms rooms → (roomKeys rooms i).length ≤ 1000

def TotalKeysBounds (rooms : Rooms) : Prop :=
  1 ≤ totalKeys rooms ∧ totalKeys rooms ≤ 3000

def KeysAreIndices (rooms : Rooms) : Prop :=
  ∀ i : ℕ, i < numRooms rooms → ∀ k ∈ roomKeys rooms i, 0 ≤ k ∧ k < (numRooms rooms : ℤ)

def RowsPairwiseDistinct (rooms : Rooms) : Prop :=
  ∀ i : ℕ, i < numRooms rooms → (roomKeys rooms i).Nodup

def Pre (rooms : Rooms) : Prop :=
  LenBounds rooms ∧ RowLenBounds rooms ∧ TotalKeysBounds rooms ∧ KeysAreIndices rooms ∧
    RowsPairwiseDistinct rooms

def ClosedUnderKeys (rooms : Rooms) (S : Set ℤ) : Prop :=
  ∀ i : ℕ, i < numRooms rooms → (i : ℤ) ∈ S → ∀ k ∈ roomKeys rooms i, k ∈ S

def Reach (rooms : Rooms) : Set ℤ :=
  {x | ∀ S : Set ℤ, (0 : ℤ) ∈ S → ClosedUnderKeys rooms S → x ∈ S}

def VisitsAllReachable (rooms : Rooms) : Prop :=
  ∀ j : ℕ, j < numRooms rooms → (j : ℤ) ∈ Reach rooms

def IsIndexSet (rooms : Rooms) (S : Set ℤ) : Prop :=
  ∀ x ∈ S, ∃ i : ℕ, i < numRooms rooms ∧ (i : ℤ) = x

def IsObstruction (rooms : Rooms) : Prop :=
  ∃ S : Set ℤ, IsIndexSet rooms S ∧ (0 : ℤ) ∈ S ∧
    (∃ j : ℕ, j < numRooms rooms ∧ (j : ℤ) ∉ S) ∧ ClosedUnderKeys rooms S

def removeZeros (l : List ℤ) : List ℤ := l.filter (fun k => decide (k ≠ 0))

def IsVisitOrder (rooms : Rooms) (order : List ℕ) : Prop :=
  order.length = numRooms rooms ∧
    (∀ x ∈ order, x < numRooms rooms) ∧
    order.Nodup ∧
    order.head? = some 0 ∧
    (∀ t : ℕ, 1 ≤ t → t < numRooms rooms →
      ∃ s : ℕ, s < t ∧ ((order[t]!) : ℤ) ∈ roomKeys rooms (order[s]!))

/-- The function returns a result r (it does not fail) and r = true if and only if every index j with 0 <= j < len(rooms) belongs to Reach(rooms), where Reach(rooms) is the smallest set S of indices such that 0 ∈ S and, for every i ∈ S, every key k in rooms[i] also belongs to S.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct. -/
theorem spec_1 (rooms : Rooms) (h : Pre rooms) :
    ∃ r : Bool, can_visit_all_rooms rooms = ok r ∧ (r = true ↔ VisitsAllReachable rooms) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms), ∃ r : Bool, can_visit_all_rooms rooms = ok r ∧ (r = true ↔ VisitsAllReachable rooms)) := by
  sorry

/-- The function returns a result r (a Bool); it does not fail under these preconditions.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct. -/
theorem spec_2 (rooms : Rooms) (h : Pre rooms) :
    ∃ r : Bool, can_visit_all_rooms rooms = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms), ∃ r : Bool, can_visit_all_rooms rooms = ok r) := by
  sorry

/-- The function returns true.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct; and for every j with 1 <= j < len(rooms), j ∈ rooms[0]. -/
theorem spec_3 (rooms : Rooms) (h : Pre rooms)
    (hkeys : ∀ j : ℕ, 1 ≤ j → j < numRooms rooms → ((j : ℤ) ∈ roomKeys rooms 0)) :
    can_visit_all_rooms rooms = ok true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms)
    (hkeys : ∀ j : ℕ, 1 ≤ j → j < numRooms rooms → ((j : ℤ) ∈ roomKeys rooms 0)), can_visit_all_rooms rooms = ok true) := by
  sorry

/-- The function returns false.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct; and len(rooms[0]) = 0. -/
theorem spec_4 (rooms : Rooms) (h : Pre rooms) (h0 : (roomKeys rooms 0).length = 0) :
    can_visit_all_rooms rooms = ok false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms) (h0 : (roomKeys rooms 0).length = 0), can_visit_all_rooms rooms = ok false) := by
  sorry

/-- The function returns the same Bool on rooms and on rooms': can_visit_all_rooms(rooms) = can_visit_all_rooms(rooms').
  Preconditions: rooms and rooms' both satisfy: 2 <= len <= 1000; for every i with 0 <= i < len, 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len; for every i with 0 <= i < len, all entries of rooms[i] are pairwise distinct. Additionally, len(rooms) = len(rooms') = n, and for every i with 0 <= i < n, rooms'[i] is a permutation of rooms[i]. -/
theorem spec_5 (rooms rooms' : Rooms) (h : Pre rooms) (h' : Pre rooms')
    (hlen : numRooms rooms = numRooms rooms')
    (hperm : ∀ i : ℕ, i < numRooms rooms → List.Perm (roomKeys rooms i) (roomKeys rooms' i)) :
    can_visit_all_rooms rooms = can_visit_all_rooms rooms' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rooms rooms' : Rooms) (h : Pre rooms) (h' : Pre rooms')
    (hlen : numRooms rooms = numRooms rooms')
    (hperm : ∀ i : ℕ, i < numRooms rooms → List.Perm (roomKeys rooms i) (roomKeys rooms' i)), can_visit_all_rooms rooms = can_visit_all_rooms rooms') := by
  sorry

/-- can_visit_all_rooms(rooms) = can_visit_all_rooms(rooms').
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct. Let rooms' be obtained from rooms by removing every occurrence of the value 0 from every rooms[i]. Assume rooms' also satisfies the constraints (in particular the total number of remaining keys is at least 1). -/
theorem spec_6 (rooms rooms' : Rooms) (h : Pre rooms) (h' : Pre rooms')
    (hlen : numRooms rooms = numRooms rooms')
    (hrm : ∀ i : ℕ, i < numRooms rooms → roomKeys rooms' i = removeZeros (roomKeys rooms i)) :
    can_visit_all_rooms rooms = can_visit_all_rooms rooms' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rooms rooms' : Rooms) (h : Pre rooms) (h' : Pre rooms')
    (hlen : numRooms rooms = numRooms rooms')
    (hrm : ∀ i : ℕ, i < numRooms rooms → roomKeys rooms' i = removeZeros (roomKeys rooms i)), can_visit_all_rooms rooms = can_visit_all_rooms rooms') := by
  sorry

/-- For every pair of inputs rooms and rooms' satisfying the preconditions, both calls return a Bool (they do not fail), and if can_visit_all_rooms(rooms) returns true, then can_visit_all_rooms(rooms') returns true.
  Preconditions: rooms and rooms' both satisfy: 2 <= len <= 1000; for every i with 0 <= i < len, 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len; for every i with 0 <= i < len, all entries of rooms[i] are pairwise distinct. Additionally, len(rooms) = len(rooms') = n, and for every i with 0 <= i < n, every key in rooms[i] is also in rooms'[i] (i.e., rooms[i] ⊆ rooms'[i] as sets). -/
theorem spec_7 (rooms rooms' : Rooms) (h : Pre rooms) (h' : Pre rooms')
    (hlen : numRooms rooms = numRooms rooms')
    (hsub : ∀ i : ℕ, i < numRooms rooms → ∀ k ∈ roomKeys rooms i, k ∈ roomKeys rooms' i) :
    (∃ r : Bool, can_visit_all_rooms rooms = ok r) ∧
      (∃ r' : Bool, can_visit_all_rooms rooms' = ok r') ∧
      (can_visit_all_rooms rooms = ok true → can_visit_all_rooms rooms' = ok true) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rooms rooms' : Rooms) (h : Pre rooms) (h' : Pre rooms')
    (hlen : numRooms rooms = numRooms rooms')
    (hsub : ∀ i : ℕ, i < numRooms rooms → ∀ k ∈ roomKeys rooms i, k ∈ roomKeys rooms' i), (∃ r : Bool, can_visit_all_rooms rooms = ok r) ∧
      (∃ r' : Bool, can_visit_all_rooms rooms' = ok r') ∧
      (can_visit_all_rooms rooms = ok true → can_visit_all_rooms rooms' = ok true)) := by
  sorry

/-- Whenever the function returns false, there exists a set S ⊆ {0, 1, ..., len(rooms)-1} such that 0 ∈ S, S ≠ {0, 1, ..., len(rooms)-1} (i.e., there is some j with 0 <= j < len(rooms) and j ∉ S), and for every i ∈ S, every key k in rooms[i] also belongs to S.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct. -/
theorem spec_8 (rooms : Rooms) (h : Pre rooms)
    (hfalse : can_visit_all_rooms rooms = ok false) :
    ∃ S : Set ℤ, IsIndexSet rooms S ∧ (0 : ℤ) ∈ S ∧
      (∃ j : ℕ, j < numRooms rooms ∧ (j : ℤ) ∉ S) ∧ ClosedUnderKeys rooms S := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms)
    (hfalse : can_visit_all_rooms rooms = ok false), ∃ S : Set ℤ, IsIndexSet rooms S ∧ (0 : ℤ) ∈ S ∧
      (∃ j : ℕ, j < numRooms rooms ∧ (j : ℤ) ∉ S) ∧ ClosedUnderKeys rooms S) := by
  sorry

/-- The function returns false if and only if there exists a set S ⊆ {0, 1, ..., len(rooms)-1} such that 0 ∈ S, S ≠ {0, 1, ..., len(rooms)-1}, and for every i ∈ S, every key k in rooms[i] also belongs to S.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct. -/
theorem spec_9 (rooms : Rooms) (h : Pre rooms) :
    (can_visit_all_rooms rooms = ok false ↔ IsObstruction rooms) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms), (can_visit_all_rooms rooms = ok false ↔ IsObstruction rooms)) := by
  sorry

/-- The function returns true if and only if there exists a permutation (i_0, i_1, ..., i_{n-1}) of {0, 1, ..., n-1}, where n = len(rooms) and i_0 = 0, such that for every t with 1 <= t < n, i_t belongs to the union of the sets rooms[i_s] over all s with 0 <= s < t.
  Preconditions: 2 <= len(rooms) <= 1000; for every i with 0 <= i < len(rooms), 0 <= len(rooms[i]) <= 1000; 1 <= sum_{i=0}^{len(rooms)-1} len(rooms[i]) <= 3000; for every i with 0 <= i < len(rooms) and every j with 0 <= j < len(rooms[i]), 0 <= rooms[i][j] < len(rooms); for every i with 0 <= i < len(rooms), all entries of rooms[i] are pairwise distinct. -/
theorem spec_10 (rooms : Rooms) (h : Pre rooms) :
    (can_visit_all_rooms rooms = ok true ↔ ∃ order : List ℕ, IsVisitOrder rooms order) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rooms : Rooms) (h : Pre rooms), (can_visit_all_rooms rooms = ok true ↔ ∃ order : List ℕ, IsVisitOrder rooms order)) := by
  sorry

end AegisSpec.CanVisitAllRooms
