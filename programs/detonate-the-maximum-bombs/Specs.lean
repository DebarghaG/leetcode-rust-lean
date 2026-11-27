import Aegis.MaximumDetonation.Code.Funs

/-!
# Specifications of `Aegis.MaximumDetonation.maximum_detonation`

LeetCode problem `detonate-the-maximum-bombs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumDetonation

  open Aegis.MaximumDetonation (maximum_detonation)

  def rows (bombs : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    bombs.val.map (fun v => v.val.map (fun x => x.val))

  def row (bombs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    (rows bombs).getD i []

  def xcoord (bombs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    (row bombs i).getD 0 0

  def ycoord (bombs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    (row bombs i).getD 1 0

  def radius (bombs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    (row bombs i).getD 2 0

  def edge (bombs : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
    (xcoord bombs i - xcoord bombs j) ^ 2 + (ycoord bombs i - ycoord bombs j) ^ 2 ≤
      (radius bombs i) ^ 2

  def reaches (bombs : Slice (alloc.vec.Vec Std.I64)) (n i j : Nat) : Prop :=
    Relation.ReflTransGen (fun a b : Nat => a < n ∧ b < n ∧ edge bombs a b) i j

  noncomputable def reachSet (bombs : Slice (alloc.vec.Vec Std.I64)) (n i : Nat) : Finset Nat := by
    classical
    exact (Finset.range n).filter (fun j => reaches bombs n i j)

  noncomputable def reachCard (bombs : Slice (alloc.vec.Vec Std.I64)) (n i : Nat) : Nat :=
    (reachSet bombs n i).card

  noncomputable def maxReachCard (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Nat :=
    (Finset.range n).sup (fun s => reachCard bombs n s)

  structure BombsInv (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop where

    len_eq : bombs.val.length = n

    n_pos : 1 ≤ n

    n_le : n ≤ 100

    row_length : ∀ i, i < n → (row bombs i).length = 3

    x_lower : ∀ i, i < n → 1 ≤ xcoord bombs i

    x_upper : ∀ i, i < n → xcoord bombs i ≤ 100000

    y_lower : ∀ i, i < n → 1 ≤ ycoord bombs i

    y_upper : ∀ i, i < n → ycoord bombs i ≤ 100000

    r_lower : ∀ i, i < n → 1 ≤ radius bombs i

    r_upper : ∀ i, i < n → radius bombs i ≤ 100000

  def PairwiseNoEdge (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    ∀ i, i < n → ∀ j, j < n → i ≠ j →
      (radius bombs i) ^ 2 <
        (xcoord bombs i - xcoord bombs j) ^ 2 + (ycoord bombs i - ycoord bombs j) ^ 2

  def DetonatesAll (bombs : Slice (alloc.vec.Vec Std.I64)) (n i : Nat) : Prop :=
    i < n ∧ ∀ j, j < n → j ≠ i →
      (xcoord bombs i - xcoord bombs j) ^ 2 + (ycoord bombs i - ycoord bombs j) ^ 2 ≤
        (radius bombs i) ^ 2

  def coincidentCount (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (X Y : Int) : Nat :=
    ((Finset.range n).filter (fun i => xcoord bombs i = X ∧ ycoord bombs i = Y)).card

  def permuteRows (r : List (List Int)) (n : Nat) (pi : Fin n → Nat) : List (List Int) :=
    List.ofFn (fun k : Fin n => r.getD (pi k) [])

  def shiftRows (r : List (List Int)) (a b : Int) : List (List Int) :=
    r.map (fun row =>
      match row with
      | x :: y :: rad :: rest => (x + a) :: (y + b) :: rad :: rest
      | _ => row)

  def scaleRows (r : List (List Int)) (c : Int) : List (List Int) :=
    r.map (fun row => row.map (fun v => c * v))

  /-- The function returns a result r (it does not fail) and r = max over s in [0,n) of |Reach(s)|, where for indices i,j in [0,n) we write edge(i,j) iff (bombs[i][0] - bombs[j][0])^2 + (bombs[i][1] - bombs[j][1])^2 <= (bombs[i][2])^2, and Reach(s) is the set of indices j for which there exist k >= 0 and indices p_0, ..., p_k with p_0 = s, p_k = j, and edge(p_t, p_{t+1}) for every 0 <= t < k.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_1 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        r.val = ((maxReachCard bombs n : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          r.val = ((maxReachCard bombs n : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_2 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= n.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_3 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ r.val ≤ (n : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ r.val ≤ (n : Int)) := by
    sorry

  /-- The function returns a result r and there exists an index s with 0 <= s < n such that r = |Reach(s)|, where Reach(s) is the least subset of [0,n) that contains s and is closed under the rule that if i is in the subset and (bombs[i][0] - bombs[j][0])^2 + (bombs[i][1] - bombs[j][1])^2 <= (bombs[i][2])^2, then j is also in the subset.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_4 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∃ s : Nat, s < n ∧ r.val = ((reachCard bombs n s : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∃ s : Nat, s < n ∧ r.val = ((reachCard bombs n s : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and for every index s with 0 <= s < n, |Reach(s)| <= r, where Reach(s) is the set of bombs detonated when starting at s: the least subset of [0,n) containing s and closed under direct detonation, i.e. if i is in the subset and (bombs[i][0] - bombs[j][0])^2 + (bombs[i][1] - bombs[j][1])^2 <= (bombs[i][2])^2, then j is in the subset.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_5 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∀ s : Nat, s < n → ((reachCard bombs n s : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∀ s : Nat, s < n → ((reachCard bombs n s : Nat) : Int) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: n = len(bombs) satisfies 2 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. For every ordered pair (i,j) with 0 <= i < n, 0 <= j < n, and i != j, (bombs[i][0] - bombs[j][0])^2 + (bombs[i][1] - bombs[j][1])^2 > (bombs[i][2])^2. -/
  theorem spec_6 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (h : BombsInv bombs n) (hn : 2 ≤ n) (hno : PairwiseNoEdge bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (h : BombsInv bombs n) (hn : 2 ≤ n) (hno : PairwiseNoEdge bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = n.
    Preconditions: n = len(bombs) satisfies 2 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. There exists an index s with 0 <= s < n such that for every j with 0 <= j < n and j != s, (bombs[s][0] - bombs[j][0])^2 + (bombs[s][1] - bombs[j][1])^2 <= (bombs[s][2])^2. -/
  theorem spec_7 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (h : BombsInv bombs n) (hn : 2 ≤ n)
      (hw : ∃ s : Nat, DetonatesAll bombs n s) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ r.val = (n : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (h : BombsInv bombs n) (hn : 2 ≤ n)
        (hw : ∃ s : Nat, DetonatesAll bombs n s), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧ r.val = (n : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_8 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r) := by
    sorry

  /-- The function returns a result r. For every permutation pi of [0,n), let bombs_pi be the list of length n with bombs_pi[k] = bombs[pi(k)] for 0 <= k < n. The function returns a result r_pi on bombs_pi, and r_pi = r.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_9 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∀ (pi : Equiv.Perm (Fin n)) (bombs_pi : Slice (alloc.vec.Vec Std.I64)),
          rows bombs_pi = permuteRows (rows bombs) n (fun k => (pi k).val) →
          ∃ r_pi : Std.I64, maximum_detonation bombs_pi = ok r_pi ∧ r_pi.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∀ (pi : Equiv.Perm (Fin n)) (bombs_pi : Slice (alloc.vec.Vec Std.I64)),
            rows bombs_pi = permuteRows (rows bombs) n (fun k => (pi k).val) →
            ∃ r_pi : Std.I64, maximum_detonation bombs_pi = ok r_pi ∧ r_pi.val = r.val) := by
    sorry

  /-- The function returns a result r. For every pair of integers (a,b) such that for every i with 0 <= i < n, 1 <= bombs[i][0] + a <= 100000 and 1 <= bombs[i][1] + b <= 100000, let bombs_shift be the list of length n with bombs_shift[i] = [bombs[i][0] + a, bombs[i][1] + b, bombs[i][2]] for 0 <= i < n. The function returns a result r_shift on bombs_shift, and r_shift = r.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_10 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∀ (a b : Int),
          (∀ i, i < n → 1 ≤ xcoord bombs i + a ∧ xcoord bombs i + a ≤ 100000) →
          (∀ i, i < n → 1 ≤ ycoord bombs i + b ∧ ycoord bombs i + b ≤ 100000) →
          ∀ bombs_shift : Slice (alloc.vec.Vec Std.I64),
            rows bombs_shift = shiftRows (rows bombs) a b →
            ∃ r_shift : Std.I64,
              maximum_detonation bombs_shift = ok r_shift ∧ r_shift.val = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∀ (a b : Int),
            (∀ i, i < n → 1 ≤ xcoord bombs i + a ∧ xcoord bombs i + a ≤ 100000) →
            (∀ i, i < n → 1 ≤ ycoord bombs i + b ∧ ycoord bombs i + b ≤ 100000) →
            ∀ bombs_shift : Slice (alloc.vec.Vec Std.I64),
              rows bombs_shift = shiftRows (rows bombs) a b →
              ∃ r_shift : Std.I64,
                maximum_detonation bombs_shift = ok r_shift ∧ r_shift.val = r.val) := by
    sorry

  /-- The function returns a result r. For every positive integer c such that for every i with 0 <= i < n, 1 <= c * bombs[i][0] <= 100000, 1 <= c * bombs[i][1] <= 100000, and 1 <= c * bombs[i][2] <= 100000, let bombs_scaled be the list of length n with bombs_scaled[i] = [c * bombs[i][0], c * bombs[i][1], c * bombs[i][2]] for 0 <= i < n. The function returns a result r_scaled on bombs_scaled, and r_scaled = r.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_11 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∀ (c : Int), 0 < c →
          (∀ i, i < n → 1 ≤ c * xcoord bombs i ∧ c * xcoord bombs i ≤ 100000) →
          (∀ i, i < n → 1 ≤ c * ycoord bombs i ∧ c * ycoord bombs i ≤ 100000) →
          (∀ i, i < n → 1 ≤ c * radius bombs i ∧ c * radius bombs i ≤ 100000) →
          ∀ bombs_scaled : Slice (alloc.vec.Vec Std.I64),
            rows bombs_scaled = scaleRows (rows bombs) c →
            ∃ r_scaled : Std.I64,
              maximum_detonation bombs_scaled = ok r_scaled ∧ r_scaled.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∀ (c : Int), 0 < c →
            (∀ i, i < n → 1 ≤ c * xcoord bombs i ∧ c * xcoord bombs i ≤ 100000) →
            (∀ i, i < n → 1 ≤ c * ycoord bombs i ∧ c * ycoord bombs i ≤ 100000) →
            (∀ i, i < n → 1 ≤ c * radius bombs i ∧ c * radius bombs i ≤ 100000) →
            ∀ bombs_scaled : Slice (alloc.vec.Vec Std.I64),
              rows bombs_scaled = scaleRows (rows bombs) c →
              ∃ r_scaled : Std.I64,
                maximum_detonation bombs_scaled = ok r_scaled ∧ r_scaled.val = r.val) := by
    sorry

  /-- The function returns a result r. If n <= 99, then for every triple of integers (x,y,radius) such that 1 <= x <= 100000, 1 <= y <= 100000, 1 <= radius <= 100000, and for every i with 0 <= i < n, (x - bombs[i][0])^2 + (y - bombs[i][1])^2 > radius^2 and (bombs[i][0] - x)^2 + (bombs[i][1] - y)^2 > (bombs[i][2])^2, let bombs_ext be the list of length n+1 with bombs_ext[i] = bombs[i] for 0 <= i < n and bombs_ext[n] = [x, y, radius]. The function returns a result r_ext on bombs_ext, and r_ext = r.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_12 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        (n ≤ 99 →
          ∀ (x y rad : Int) (bombs_ext : Slice (alloc.vec.Vec Std.I64)),
            1 ≤ x → x ≤ 100000 → 1 ≤ y → y ≤ 100000 → 1 ≤ rad → rad ≤ 100000 →
            (∀ i, i < n → rad ^ 2 < (x - xcoord bombs i) ^ 2 + (y - ycoord bombs i) ^ 2) →
            (∀ i, i < n →
              (radius bombs i) ^ 2 <
                (xcoord bombs i - x) ^ 2 + (ycoord bombs i - y) ^ 2) →
            rows bombs_ext = rows bombs ++ [[x, y, rad]] →
            ∃ r_ext : Std.I64,
              maximum_detonation bombs_ext = ok r_ext ∧ r_ext.val = r.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          (n ≤ 99 →
            ∀ (x y rad : Int) (bombs_ext : Slice (alloc.vec.Vec Std.I64)),
              1 ≤ x → x ≤ 100000 → 1 ≤ y → y ≤ 100000 → 1 ≤ rad → rad ≤ 100000 →
              (∀ i, i < n → rad ^ 2 < (x - xcoord bombs i) ^ 2 + (y - ycoord bombs i) ^ 2) →
              (∀ i, i < n →
                (radius bombs i) ^ 2 <
                  (xcoord bombs i - x) ^ 2 + (ycoord bombs i - y) ^ 2) →
              rows bombs_ext = rows bombs ++ [[x, y, rad]] →
              ∃ r_ext : Std.I64,
                maximum_detonation bombs_ext = ok r_ext ∧ r_ext.val = r.val)) := by
    sorry

  /-- The function returns a result r. For every list bombs2 of length n such that for every i with 0 <= i < n, bombs2[i] has length 3, bombs2[i][0] = bombs[i][0], bombs2[i][1] = bombs[i][1], bombs[i][2] <= bombs2[i][2], and 1 <= bombs2[i][2] <= 100000, the function returns a result r2 on bombs2, and r2 >= r.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_13 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∀ bombs2 : Slice (alloc.vec.Vec Std.I64),
          bombs2.val.length = n →
          (∀ i, i < n → (row bombs2 i).length = 3) →
          (∀ i, i < n → xcoord bombs2 i = xcoord bombs i) →
          (∀ i, i < n → ycoord bombs2 i = ycoord bombs i) →
          (∀ i, i < n → radius bombs i ≤ radius bombs2 i) →
          (∀ i, i < n → 1 ≤ radius bombs2 i ∧ radius bombs2 i ≤ 100000) →
          ∃ r2 : Std.I64, maximum_detonation bombs2 = ok r2 ∧ r.val ≤ r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∀ bombs2 : Slice (alloc.vec.Vec Std.I64),
            bombs2.val.length = n →
            (∀ i, i < n → (row bombs2 i).length = 3) →
            (∀ i, i < n → xcoord bombs2 i = xcoord bombs i) →
            (∀ i, i < n → ycoord bombs2 i = ycoord bombs i) →
            (∀ i, i < n → radius bombs i ≤ radius bombs2 i) →
            (∀ i, i < n → 1 ≤ radius bombs2 i ∧ radius bombs2 i ≤ 100000) →
            ∃ r2 : Std.I64, maximum_detonation bombs2 = ok r2 ∧ r.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r and for every pair of integers (X,Y), if m is the number of indices i with 0 <= i < n, bombs[i][0] = X, and bombs[i][1] = Y, then r >= m.
    Preconditions: n = len(bombs) satisfies 1 <= n <= 100. For every i with 0 <= i < n, bombs[i] has length 3, and 1 <= bombs[i][0] <= 100000, 1 <= bombs[i][1] <= 100000, 1 <= bombs[i][2] <= 100000. -/
  theorem spec_14 (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n) :
      ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
        ∀ (X Y : Int), ((coincidentCount bombs n X Y : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (bombs : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : BombsInv bombs n), ∃ r : Std.I64, maximum_detonation bombs = ok r ∧
          ∀ (X Y : Int), ((coincidentCount bombs n X Y : Nat) : Int) ≤ r.val) := by
    sorry

  end AegisSpec.MaximumDetonation
