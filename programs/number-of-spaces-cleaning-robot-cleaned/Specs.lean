import Aegis.NumberOfCleanRooms.Code.Funs

/-!
# Specifications of `Aegis.NumberOfCleanRooms.number_of_clean_rooms`

LeetCode problem `number-of-spaces-cleaning-robot-cleaned`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  attribute [local instance] Classical.propDecidable

  namespace AegisSpec.NumberOfCleanRooms

  def FirstIndex (P : Nat → Prop) (lo n k : Nat) : Prop :=
    (k = n ∧ ∀ j, lo ≤ j → j < n → ¬ P j) ∨
      (lo ≤ k ∧ k < n ∧ P k ∧ ∀ j, lo ≤ j → j < k → ¬ P j)

  def MaxPrefix (P : Nat → Prop) (n k : Nat) : Prop :=
    k < n ∧ (∀ j, j ≤ k → P j) ∧ ∀ k', k' < n → (∀ j, j ≤ k' → P j) → k' ≤ k

  def Adjacent (p q : Nat × Nat) : Prop :=
    ((p.1 : Int) - (q.1 : Int)).natAbs + ((p.2 : Int) - (q.2 : Int)).natAbs = 1

  def Chain (S : Nat × Nat → Prop) : Nat × Nat → List (Nat × Nat) → Nat × Nat → Prop
    | p, [], q => p = q ∧ S p
    | p, x :: xs, q => S p ∧ Adjacent p x ∧ Chain S x xs q

  def roomM (room : Slice (alloc.vec.Vec I64)) : Nat := room.val.length

  def roomN (room : Slice (alloc.vec.Vec I64)) : Nat :=
    match room.val with
    | [] => 0
    | row :: _ => row.val.length

  def rowLen (room : Slice (alloc.vec.Vec I64)) (r : Nat) : Nat :=
    match room.val[r]? with
    | none => 0
    | some row => row.val.length

  def cellVal (room : Slice (alloc.vec.Vec I64)) (r c : Nat) : Int :=
    match room.val[r]? with
    | none => 0
    | some row =>
      match row.val[c]? with
      | none => 0
      | some x => x.val

  abbrev State : Type := Nat × Nat × Nat

  def dr : Nat → Int
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | _ => -1

  def dc : Nat → Int
    | 0 => 1
    | 1 => 0
    | 2 => -1
    | _ => 0

  def T (room : Slice (alloc.vec.Vec I64)) (s : State) : State :=
    let r := s.1
    let c := s.2.1
    let d := s.2.2
    let r' : Int := (r : Int) + dr d
    let c' : Int := (c : Int) + dc d
    if 0 ≤ r' ∧ r' < (roomM room : Int) ∧ 0 ≤ c' ∧ c' < (roomN room : Int) ∧
        cellVal room r'.toNat c'.toNat = 0 then
      (r'.toNat, c'.toNat, d)
    else (r, c, (d + 1) % 4)

  def stateAt (room : Slice (alloc.vec.Vec I64)) (t : Nat) : State :=
    Nat.iterate (T room) t (0, 0, 0)

  def visited (room : Slice (alloc.vec.Vec I64)) (r c : Nat) : Prop :=
    ∃ t d, d < 4 ∧ stateAt room t = (r, c, d)

  noncomputable def visitedCount (room : Slice (alloc.vec.Vec I64)) : Nat :=
    (((Finset.range (roomM room)).product (Finset.range (roomN room))).filter
        (fun p : Nat × Nat => visited room p.1 p.2)).card

  noncomputable def zeroCellCount (room : Slice (alloc.vec.Vec I64)) : Nat :=
    (((Finset.range (roomM room)).product (Finset.range (roomN room))).filter
        (fun p : Nat × Nat => cellVal room p.1 p.2 = 0)).card

  /-- Let m = len(room) and n = len(room[0]). Define directions 0 = right, 1 = down, 2 = left, 3 = up, with unit vectors (dr(0),dc(0)) = (0,1), (dr(1),dc(1)) = (1,0), (dr(2),dc(2)) = (0,-1), (dr(3),dc(3)) = (-1,0). A state is a triple (r,c,d) with 0 <= r < m, 0 <= c < n, and d in {0,1,2,3}. Define the transition function T(r,c,d) as follows: let r' = r + dr(d) and c' = c + dc(d). If 0 <= r' < m and 0 <= c' < n and room[r'][c'] = 0, then T(r,c,d) = (r',c',d); otherwise T(r,c,d) = (r,c,(d+1) mod 4). Define the state sequence s_0 = (0,0,0) and s_{t+1} = T(s_t) for t >= 0. Define the set of cleaned cells Visited = { (r,c) | there exists t >= 0 and d in {0,1,2,3} such that s_t = (r,c,d) }. Then the function returns a result r and r = |Visited| (the number of distinct cells in Visited).
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300. -/
  theorem spec_1 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300) :
      ∃ res : I64,
        Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
          res.val = (visitedCount room : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300), ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            res.val = (visitedCount room : Int)) := by
    sorry

  /-- The function returns a result r (it does not panic, overflow, or fail).
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300. -/
  theorem spec_2 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300) :
      ∃ res : I64, Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300), ∃ res : I64, Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res) := by
    sorry

  /-- The returned value r satisfies r >= 1.
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300. -/
  theorem spec_3 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300) :
      ∃ res : I64,
        Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧ 1 ≤ res.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300), ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧ 1 ≤ res.val) := by
    sorry

  /-- The returned value r is at most the number of cells (r,c) with 0 <= r < m and 0 <= c < n and room[r][c] = 0.
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300. -/
  theorem spec_4 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300) :
      ∃ res : I64,
        Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
          res.val ≤ (zeroCellCount room : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300), ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            res.val ≤ (zeroCellCount room : Int)) := by
    sorry

  /-- Let k be the smallest integer with 1 <= k < n and room[0][k] = 1, if such k exists; otherwise let k = n. Then the function returns k.
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300; m = 1. -/
  theorem spec_5 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300)
      (hm1 : roomM room = 1) :
      ∀ k, FirstIndex (fun j => cellVal room 0 j = 1) 1 (roomN room) k →
        ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            res.val = (k : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300)
        (hm1 : roomM room = 1), ∀ k, FirstIndex (fun j => cellVal room 0 j = 1) 1 (roomN room) k →
          ∃ res : I64,
            Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
              res.val = (k : Int)) := by
    sorry

  /-- Let k be the smallest integer with 1 <= k < m and room[k][0] = 1, if such k exists; otherwise let k = m. Then the function returns k.
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300; n = 1. -/
  theorem spec_6 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300)
      (hn1 : roomN room = 1) :
      ∀ k, FirstIndex (fun i => cellVal room i 0 = 1) 1 (roomM room) k →
        ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            res.val = (k : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300)
        (hn1 : roomN room = 1), ∀ k, FirstIndex (fun i => cellVal room i 0 = 1) 1 (roomM room) k →
          ∃ res : I64,
            Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
              res.val = (k : Int)) := by
    sorry

  /-- The function returns 1 if and only if (n = 1 or (n > 1 and room[0][1] = 1)) and (m = 1 or (m > 1 and room[1][0] = 1)).
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300. -/
  theorem spec_7 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300) :
      ∃ res : I64,
        Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
          (res.val = 1 ↔
            (roomN room = 1 ∨ (1 < roomN room ∧ cellVal room 0 1 = 1)) ∧
              (roomM room = 1 ∨ (1 < roomM room ∧ cellVal room 1 0 = 1))) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300), ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            (res.val = 1 ↔
              (roomN room = 1 ∨ (1 < roomN room ∧ cellVal room 0 1 = 1)) ∧
                (roomM room = 1 ∨ (1 < roomM room ∧ cellVal room 1 0 = 1)))) := by
    sorry

  /-- The function returns (if m = 1 or n = 1 then m*n else 2*m + 2*n - 4).
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300; for all r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0. -/
  theorem spec_8 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300)
      (hzero : ∀ r c, r < roomM room → c < roomN room → cellVal room r c = 0) :
      ∃ res : I64,
        Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
          res.val =
            (if roomM room = 1 ∨ roomN room = 1 then
                ((roomM room * roomN room : Nat) : Int)
              else ((2 * roomM room + 2 * roomN room - 4 : Nat) : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300)
        (hzero : ∀ r c, r < roomM room → c < roomN room → cellVal room r c = 0), ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            res.val =
              (if roomM room = 1 ∨ roomN room = 1 then
                  ((roomM room * roomN room : Nat) : Int)
                else ((2 * roomM room + 2 * roomN room - 4 : Nat) : Int))) := by
    sorry

  /-- Let k be the largest integer such that 0 <= k < n and for all j with 0 <= j <= k, room[0][j] = 0. Then the returned value r satisfies r >= k + 1.
    Preconditions: room is a non-empty rectangular matrix: let m = len(room), n = len(room[0]); m >= 1, n >= 1; for every r with 0 <= r < m, len(room[r]) = n; for every r,c with 0 <= r < m and 0 <= c < n, room[r][c] = 0 or room[r][c] = 1; room[0][0] = 0; m <= 300 and n <= 300. -/
  theorem spec_9 (room : Slice (alloc.vec.Vec I64))
      (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
      (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
      (hbin : ∀ r c, r < roomM room → c < roomN room →
        cellVal room r c = 0 ∨ cellVal room r c = 1)
      (h00 : cellVal room 0 0 = 0)
      (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300) :
      ∀ k, MaxPrefix (fun j => cellVal room 0 j = 0) (roomN room) k →
        ∃ res : I64,
          Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
            (k : Int) + 1 ≤ res.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (room : Slice (alloc.vec.Vec I64))
        (hm : 1 ≤ roomM room) (hn : 1 ≤ roomN room)
        (hrect : ∀ r, r < roomM room → rowLen room r = roomN room)
        (hbin : ∀ r c, r < roomM room → c < roomN room →
          cellVal room r c = 0 ∨ cellVal room r c = 1)
        (h00 : cellVal room 0 0 = 0)
        (hm300 : roomM room ≤ 300) (hn300 : roomN room ≤ 300), ∀ k, MaxPrefix (fun j => cellVal room 0 j = 0) (roomN room) k →
          ∃ res : I64,
            Aegis.NumberOfCleanRooms.number_of_clean_rooms room = ok res ∧
              (k : Int) + 1 ≤ res.val) := by
    sorry

  end AegisSpec.NumberOfCleanRooms
