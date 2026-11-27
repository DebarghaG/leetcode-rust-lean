import Aegis.GeneratePossibleNextMoves.Code.Funs

/-!
# Specifications of `Aegis.GeneratePossibleNextMoves.generate_possible_next_moves`

LeetCode problem `flip-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GeneratePossibleNextMoves

  def byteAt (l : List Aeneas.Std.U8) (i : Nat) : Nat :=
    (l.getD i (0#u8)).val

  def nthVec (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)) (k : Nat) :
      Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 :=
    r.val.getD k default

  def nthState (r : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)) (k : Nat) :
      List Aeneas.Std.U8 :=
    (nthVec r k).val

  def IsValidMoveIndex (l : List Aeneas.Std.U8) (i : Nat) : Prop :=
    i + 1 < l.length ∧ byteAt l i = 43 ∧ byteAt l (i + 1) = 43

  def IsFlip (l : List Aeneas.Std.U8) (i : Nat) (v : List Aeneas.Std.U8) : Prop :=
    v.length = l.length ∧ byteAt v i = 45 ∧ byteAt v (i + 1) = 45 ∧
      ∀ j, j < l.length → j ≠ i → j ≠ i + 1 → byteAt v j = byteAt l j

  def countPlus (l : List Aeneas.Std.U8) : Nat :=
    ((List.range l.length).filter (fun j => decide (byteAt l j = 43))).length

  def countValidMoveIndices (l : List Aeneas.Std.U8) : Nat :=
    ((List.range l.length).filter
      (fun i => decide (i + 1 < l.length ∧ byteAt l i = 43 ∧ byteAt l (i + 1) = 43))).length

  /-- Whenever the function returns a result r, r is exactly the list of all states obtainable from s by one valid move, each appearing once, in arbitrary order. More precisely, call an index i a valid move index of s when 0 <= i, i+1 < n, and s[i] = s[i+1] = '+'. For a valid move index i, define flip(s,i) to be the byte array v of length n with v[i] = v[i+1] = '-' and v[j] = s[j] for every j with 0 <= j < n and j not in {i,i+1}. Then: (1) for every k with 0 <= k < len(r), there is a unique valid move index i of s such that r[k] = flip(s,i); and (2) for every valid move index i of s, there is a unique k with 0 <= k < len(r) such that r[k] = flip(s,i). In particular, if s has no valid move index then r is the empty list.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_1 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        (∀ k, k < r.val.length →
            ∃! i, IsValidMoveIndex s.val i ∧ IsFlip s.val i (nthState r k)) ∧
          (∀ i, IsValidMoveIndex s.val i →
            ∃! k, k < r.val.length ∧ IsFlip s.val i (nthState r k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          (∀ k, k < r.val.length →
              ∃! i, IsValidMoveIndex s.val i ∧ IsFlip s.val i (nthState r k)) ∧
            (∀ i, IsValidMoveIndex s.val i →
              ∃! k, k < r.val.length ∧ IsFlip s.val i (nthState r k))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns some result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). -/
  theorem spec_2 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∃ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∃ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every element v of r is a byte array with len(v) = n.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). -/
  theorem spec_3 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ v, v ∈ r.val → v.val.length = s.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ v, v ∈ r.val → v.val.length = s.val.length) := by
    sorry

  /-- Whenever the function returns a result r, every element v of r is a one-move successor of s: len(v) = n, and there exists an index i with 0 <= i, i+1 < n, and s[i] = s[i+1] = '+', such that v[i] = v[i+1] = '-', and v[j] = s[j] for every j with 0 <= j < n and j not in {i,i+1}.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_4 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ v, v ∈ r.val →
          v.val.length = s.val.length ∧ ∃ i, IsValidMoveIndex s.val i ∧
            byteAt v.val i = 45 ∧ byteAt v.val (i + 1) = 45 ∧
              ∀ j, j < s.val.length → j ≠ i → j ≠ i + 1 → byteAt v.val j = byteAt s.val j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ v, v ∈ r.val →
            v.val.length = s.val.length ∧ ∃ i, IsValidMoveIndex s.val i ∧
              byteAt v.val i = 45 ∧ byteAt v.val (i + 1) = 45 ∧
                ∀ j, j < s.val.length → j ≠ i → j ≠ i + 1 → byteAt v.val j = byteAt s.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i, i+1 < n, and s[i] = s[i+1] = '+', there exists k with 0 <= k < len(r) such that r[k] is the flip of s at i: len(r[k]) = n, r[k][i] = r[k][i+1] = '-', and r[k][j] = s[j] for every j with 0 <= j < n and j not in {i,i+1}.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_5 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ i, IsValidMoveIndex s.val i →
          ∃ k, k < r.val.length ∧ IsFlip s.val i (nthState r k) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ i, IsValidMoveIndex s.val i →
            ∃ k, k < r.val.length ∧ IsFlip s.val i (nthState r k)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) equals the number of indices i such that 0 <= i, i+1 < n, and s[i] = s[i+1] = '+'.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_6 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        r.val.length = countValidMoveIndices s.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          r.val.length = countValidMoveIndices s.val) := by
    sorry

  /-- Whenever the function returns a result r, the elements of r are pairwise distinct: for every k1 and k2 with 0 <= k1 < k2 < len(r), r[k1] != r[k2].
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). -/
  theorem spec_7 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ k1 k2, k1 < k2 → k2 < r.val.length → nthVec r k1 ≠ nthVec r k2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ k1 k2, k1 < k2 → k2 < r.val.length → nthVec r k1 ≠ nthVec r k2) := by
    sorry

  /-- Whenever the function returns a result r, for every element v of r, len(v) = n and the number of indices j with 0 <= j < n and v[j] = '+' equals the number of indices j with 0 <= j < n and s[j] = '+' minus 2.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_8 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ v, v ∈ r.val →
          v.val.length = s.val.length ∧ countPlus v.val = countPlus s.val - 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ v, v ∈ r.val →
            v.val.length = s.val.length ∧ countPlus v.val = countPlus s.val - 2) := by
    sorry

  /-- Whenever the function returns a result r, for every element v of r, len(v) = n and the set of indices j with 0 <= j < n and v[j] != s[j] is exactly {i,i+1} for some index i with 0 <= i, i+1 < n, and s[i] = s[i+1] = '+'. At those two positions, v[i] = v[i+1] = '-' and s[i] = s[i+1] = '+'.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_9 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ v, v ∈ r.val →
          v.val.length = s.val.length ∧ ∃ i, IsValidMoveIndex s.val i ∧
            (∀ j, j < s.val.length → (byteAt v.val j ≠ byteAt s.val j ↔ j = i ∨ j = i + 1)) ∧
              byteAt v.val i = 45 ∧ byteAt v.val (i + 1) = 45 ∧
                byteAt s.val i = 43 ∧ byteAt s.val (i + 1) = 43 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ v, v ∈ r.val →
            v.val.length = s.val.length ∧ ∃ i, IsValidMoveIndex s.val i ∧
              (∀ j, j < s.val.length → (byteAt v.val j ≠ byteAt s.val j ↔ j = i ∨ j = i + 1)) ∧
                byteAt v.val i = 45 ∧ byteAt v.val (i + 1) = 45 ∧
                  byteAt s.val i = 43 ∧ byteAt s.val (i + 1) = 43) := by
    sorry

  /-- Whenever the function returns a result r, r is the empty list if and only if s has no valid move index, i.e., there is no i with 0 <= i, i+1 < n, and s[i] = s[i+1] = '+'.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_10 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        (r.val = [] ↔ ¬ ∃ i, IsValidMoveIndex s.val i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          (r.val = [] ↔ ¬ ∃ i, IsValidMoveIndex s.val i)) := by
    sorry

  /-- Whenever the function returns a result r, if s has exactly one valid move index i (0 <= i, i+1 < n, s[i] = s[i+1] = '+'), then len(r) = 1, and the unique element r[0] satisfies len(r[0]) = n, r[0][i] = r[0][i+1] = '-', and r[0][j] = s[j] for every j with 0 <= j < n and j not in {i,i+1}.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_11 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ i, IsValidMoveIndex s.val i → (∀ i', IsValidMoveIndex s.val i' → i' = i) →
          r.val.length = 1 ∧ ∀ v, v ∈ r.val → IsFlip s.val i v.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ i, IsValidMoveIndex s.val i → (∀ i', IsValidMoveIndex s.val i' → i' = i) →
            r.val.length = 1 ∧ ∀ v, v ∈ r.val → IsFlip s.val i v.val) := by
    sorry

  /-- Whenever the function returns a result r, for every element v of r and every j with 0 <= j < len(v), v[j] is either byte 43 ('+') or byte 45 ('-').
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). Write '+' for byte 43 and '-' for byte 45. -/
  theorem spec_12 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        ∀ v, v ∈ r.val → ∀ j, j < v.val.length →
          byteAt v.val j = 43 ∨ byteAt v.val j = 45 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          ∀ v, v ∈ r.val → ∀ j, j < v.val.length →
            byteAt v.val j = 43 ∨ byteAt v.val j = 45) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= len(r) <= len(s) - 1.
    Preconditions: Let s = currentState and n = len(s). Assume 1 <= n <= 500, and for every i with 0 <= i < n, s[i] is either byte 43 ('+') or byte 45 ('-'). -/
  theorem spec_13 (s : Aeneas.Std.Slice Aeneas.Std.U8)
      (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
      (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45) :
      ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
        0 ≤ r.val.length ∧ r.val.length ≤ s.val.length - 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
        (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
        (hbytes : ∀ i, i < s.val.length → byteAt s.val i = 43 ∨ byteAt s.val i = 45), ∀ r, Aegis.GeneratePossibleNextMoves.generate_possible_next_moves s = ok r →
          0 ≤ r.val.length ∧ r.val.length ≤ s.val.length - 1) := by
    sorry

  end AegisSpec.GeneratePossibleNextMoves
