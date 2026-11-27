import Aegis.NumMovesStonesIi.Code.Funs

/-!
# Specifications of `Aegis.NumMovesStonesIi.num_moves_stones_ii`

LeetCode problem `moving-stones-until-consecutive-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumMovesStonesIi

  open Aegis.NumMovesStonesIi

  def vals (stones : Slice Std.I64) : List ℤ := stones.val.map (fun x => x.val)

  def lenS (stones : Slice Std.I64) : ℕ := stones.val.length

  def nthInt (v : alloc.vec.Vec Std.I64) (k : ℕ) : ℤ := (v.val.getD k 0#i64).val

  def bOf (stones : Slice Std.I64) : List ℤ := (vals stones).mergeSort (· ≤ ·)

  def bGet (stones : Slice Std.I64) (k : ℕ) : ℤ := (bOf stones).getD k 0

  def windowMax (b : ℕ → ℤ) (n : ℕ) : ℕ :=
    ((List.range n).flatMap (fun i => (List.range n).map (fun j => (i, j)))).foldr
      (fun p acc =>
        max acc (if p.1 ≤ p.2 ∧ b p.2 - b p.1 < (n : ℤ) then p.2 - p.1 + 1 else 0))
      0

  def M (stones : Slice Std.I64) : ℕ := windowMax (bGet stones) (lenS stones)

  def E (stones : Slice Std.I64) : ℤ :=
    bGet stones (lenS stones - 1) - bGet stones 0 + 1 - (lenS stones : ℤ)

  def L (stones : Slice Std.I64) : ℤ := bGet stones 1 - bGet stones 0 - 1

  def R (stones : Slice Std.I64) : ℤ :=
    bGet stones (lenS stones - 1) - bGet stones (lenS stones - 2) - 1

  def m (stones : Slice Std.I64) : ℤ :=
    if bGet stones (lenS stones - 1) - bGet stones 0 = (lenS stones : ℤ) - 1 then 0
    else if bGet stones (lenS stones - 1) - bGet stones 1 = (lenS stones : ℤ) - 1 ∨
            bGet stones (lenS stones - 2) - bGet stones 0 = (lenS stones : ℤ) - 1 then 1
    else max 2 ((lenS stones : ℤ) - (M stones : ℤ))

  def Mx (stones : Slice Std.I64) : ℤ := E stones - min (L stones) (R stones)

  def IsMinOrMax (l : List ℤ) (p : ℤ) : Prop :=
    (∀ x ∈ l, p ≤ x) ∨ (∀ x ∈ l, x ≤ p)

  def IsLegalMove (s t : List ℤ) : Prop :=
    ∃ p q : ℤ,
      p ∈ s ∧ q ∉ s ∧ IsMinOrMax s p ∧
        (∃ x ∈ (s.erase p) ++ [q], x < q) ∧
        (∃ y ∈ (s.erase p) ++ [q], q < y) ∧
        List.Perm t ((s.erase p) ++ [q])

  def LegalPlay (s t : List ℤ) : ℕ → Prop
    | 0 => List.Perm t s
    | (k + 1) => ∃ u : List ℤ, IsLegalMove s u ∧ LegalPlay u t k

  def AtConsecutivePositions (l : List ℤ) : Prop :=
    ∃ a : ℤ, List.Perm l (List.map (fun k : ℕ => a + (k : ℤ)) (List.range l.length))

  def HasPlayToConsecutive (s : List ℤ) (k : ℕ) : Prop :=
    ∃ t : List ℤ, LegalPlay s t k ∧ AtConsecutivePositions t

  /-- Whenever the function returns a result r, r[0] and r[1] are defined and the following holds. Let b be the strictly increasing rearrangement of stones. Define M = max { j-i+1 | 0 <= i <= j < n and b[j]-b[i] < n }. Define m = 0 if b[n-1]-b[0] = n-1; otherwise m = 1 if b[n-1]-b[1] = n-1 or b[n-2]-b[0] = n-1; otherwise m = max(2, n-M). Define E = b[n-1]-b[0]+1-n, L = b[1]-b[0]-1, R = b[n-1]-b[n-2]-1, and Mx = E - min(L,R). Then r[0] = m and r[1] = Mx.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_1 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧ nthInt r 0 = m stones ∧ nthInt r 1 = Mx stones := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧ nthInt r 0 = m stones ∧ nthInt r 1 = Mx stones) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_2 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∃ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∃ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_3 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r → r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r, let E = b[n-1]-b[0]+1-n, L = b[1]-b[0]-1, and R = b[n-1]-b[n-2]-1. Then r[1] = E - min(L,R).
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. Let b be the strictly increasing rearrangement of stones. -/
  theorem spec_4 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧ nthInt r 1 = E stones - min (L stones) (R stones) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧ nthInt r 1 = E stones - min (L stones) (R stones)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r[0] <= n-1.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_5 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧ 0 ≤ nthInt r 0 ∧ nthInt r 0 ≤ (lenS stones : ℤ) - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧ 0 ≤ nthInt r 0 ∧ nthInt r 0 ≤ (lenS stones : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r[1] <= b[n-1]-b[0]+1-n.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. Let b be the strictly increasing rearrangement of stones. -/
  theorem spec_6 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧ 0 ≤ nthInt r 1 ∧ nthInt r 1 ≤ E stones := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧ 0 ≤ nthInt r 1 ∧ nthInt r 1 ≤ E stones) := by
    sorry

  /-- Whenever the function returns a result r, r[0] <= r[1].
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_7 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧ nthInt r 0 ≤ nthInt r 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧ nthInt r 0 ≤ nthInt r 1) := by
    sorry

  /-- Whenever the call on stones returns r and the call on p returns r_p, r = r_p.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. Let p be any slice of length n whose entries are a permutation of the entries of stones. -/
  theorem spec_8 (stones p : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9)
      (hp_len : p.val.length = stones.val.length)
      (hp_perm : List.Perm (vals p) (vals stones)) :
      ∀ r rp : alloc.vec.Vec Std.I64,
        num_moves_stones_ii stones = ok r → num_moves_stones_ii p = ok rp → r = rp := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (stones p : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9)
        (hp_len : p.val.length = stones.val.length)
        (hp_perm : List.Perm (vals p) (vals stones)), ∀ r rp : alloc.vec.Vec Std.I64,
          num_moves_stones_ii stones = ok r → num_moves_stones_ii p = ok rp → r = rp) := by
    sorry

  /-- Whenever the call on stones returns r and the call on s' returns r', r = r'.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. Let c be an integer such that 1 <= stones[i]+c <= 10^9 for every i, and let s' be the slice defined by s'[i] = stones[i]+c. -/
  theorem spec_9 (stones s' : Slice Std.I64) (c : ℤ)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9)
      (hc_range : ∀ x ∈ vals stones, 1 ≤ x + c ∧ x + c ≤ (10 : ℤ) ^ 9)
      (hs' : vals s' = (vals stones).map (· + c)) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        num_moves_stones_ii stones = ok r → num_moves_stones_ii s' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (stones s' : Slice Std.I64) (c : ℤ)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9)
        (hc_range : ∀ x ∈ vals stones, 1 ≤ x + c ∧ x + c ≤ (10 : ℤ) ^ 9)
        (hs' : vals s' = (vals stones).map (· + c)), ∀ r r' : alloc.vec.Vec Std.I64,
          num_moves_stones_ii stones = ok r → num_moves_stones_ii s' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, there exists a legal play of exactly r[0] moves starting from stones and ending with the stones at n consecutive integer positions. A legal move takes a stone whose current position is the minimum or maximum of the current stone positions and moves it to an unoccupied integer position at which it is neither the minimum nor the maximum of the new set of stone positions.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_10 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧
          ∃ k : ℕ, nthInt r 0 = (k : ℤ) ∧ HasPlayToConsecutive (vals stones) k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧
            ∃ k : ℕ, nthInt r 0 = (k : ℤ) ∧ HasPlayToConsecutive (vals stones) k) := by
    sorry

  /-- Whenever the function returns a result r, there exists a legal play of exactly r[1] moves starting from stones and ending with the stones at n consecutive integer positions, where a legal move takes a stone whose current position is the minimum or maximum of the current stone positions and moves it to an unoccupied integer position at which it is neither the minimum nor the maximum of the new set of stone positions.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_11 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧
          ∃ k : ℕ, nthInt r 1 = (k : ℤ) ∧ HasPlayToConsecutive (vals stones) k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧
            ∃ k : ℕ, nthInt r 1 = (k : ℤ) ∧ HasPlayToConsecutive (vals stones) k) := by
    sorry

  /-- Whenever the function returns a result r, every legal play that starts from stones and ends with the stones at n consecutive integer positions has length at most r[1], where a legal move takes a stone whose current position is the minimum or maximum of the current stone positions and moves it to an unoccupied integer position at which it is neither the minimum nor the maximum of the new set of stone positions.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_12 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧
          ∀ k : ℕ, HasPlayToConsecutive (vals stones) k → (k : ℤ) ≤ nthInt r 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧
            ∀ k : ℕ, HasPlayToConsecutive (vals stones) k → (k : ℤ) ≤ nthInt r 1) := by
    sorry

  /-- Whenever the function returns a result r, every legal play that starts from stones and ends with the stones at n consecutive integer positions has length at least r[0], where a legal move takes a stone whose current position is the minimum or maximum of the current stone positions and moves it to an unoccupied integer position at which it is neither the minimum nor the maximum of the new set of stone positions.
    Preconditions: Let n = len(stones). Assume 3 <= n <= 10000, all entries of stones are distinct, and 1 <= stones[i] <= 10^9 for every 0 <= i < n. -/
  theorem spec_13 (stones : Slice Std.I64)
      (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
      (hnodup : (vals stones).Nodup)
      (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9) :
      ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
        2 ≤ r.val.length ∧
          ∀ k : ℕ, HasPlayToConsecutive (vals stones) k → nthInt r 0 ≤ (k : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 3 ≤ lenS stones) (hlen_hi : lenS stones ≤ 10000)
        (hnodup : (vals stones).Nodup)
        (hrange : ∀ x ∈ vals stones, 1 ≤ x ∧ x ≤ (10 : ℤ) ^ 9), ∀ r : alloc.vec.Vec Std.I64, num_moves_stones_ii stones = ok r →
          2 ≤ r.val.length ∧
            ∀ k : ℕ, HasPlayToConsecutive (vals stones) k → nthInt r 0 ≤ (k : ℤ)) := by
    sorry

  end AegisSpec.NumMovesStonesIi
