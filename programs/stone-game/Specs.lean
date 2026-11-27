import Aegis.StoneGame.Code.Funs

/-!
# Specifications of `Aegis.StoneGame.stone_game`

LeetCode problem `stone-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.StoneGame

def vals (piles : Slice Std.I64) : List Int := piles.val.map (fun x => (x : Int))

def entry (a : List Int) (i : Nat) : Int := a.getD i 0

def Dlen (a : List Int) (l : Nat) : Nat → Int
  | 0 => 0
  | m + 1 =>
    if m = 0 then entry a l
    else max (entry a l - Dlen a (l + 1) m) (entry a (l + m) - Dlen a l m)

def D (a : List Int) (l r : Nat) : Int := Dlen a l (r + 1 - l)

abbrev Strategy := List Int → Bool

structure Play where

  alice : Int

  bob : Int

def popRight : List Int → Option (Int × List Int)
  | [] => none
  | [x] => some (x, [])
  | x :: y :: rest =>
    match popRight (y :: rest) with
    | none => none
    | some (v, l) => some (v, x :: l)

def playAux (σ τ : Strategy) : Nat → Bool → Int → Int → List Int → Play
  | 0, _, al, bo, _ => ⟨al, bo⟩
  | m + 1, aliceTurn, al, bo, row =>
    match row with
    | [] => ⟨al, bo⟩
    | x :: rest =>
      if (if aliceTurn then σ row else τ row) then
        playAux σ τ m (!aliceTurn) (if aliceTurn then al + x else al)
          (if aliceTurn then bo else bo + x) rest
      else
        match popRight row with
        | none => ⟨al, bo⟩
        | some (v, r) =>
          playAux σ τ m (!aliceTurn) (if aliceTurn then al + v else al)
            (if aliceTurn then bo else bo + v) r

def play (σ τ : Strategy) (row : List Int) : Play := playAux σ τ row.length true 0 0 row

def IsGameValue (a : List Int) (d : Int) : Prop :=
  (∃ σ : Strategy, ∀ τ : Strategy, (play σ τ a).alice - (play σ τ a).bob ≥ d) ∧
  (∃ τ : Strategy, ∀ σ : Strategy, (play σ τ a).alice - (play σ τ a).bob ≤ d)

def aliceTotal (a : List Int) : Int := (a.sum + D a 0 (a.length - 1)) / 2

def sumEven : List Int → Int
  | [] => 0
  | [x] => x
  | x :: _ :: rest => x + sumEven rest

def sumOdd : List Int → Int
  | [] => 0
  | [_] => 0
  | _ :: y :: rest => y + sumOdd rest

/-- The function returns Result.ok true. Let n = len(piles). For 0 <= l <= r < n, define D(l, r) by: D(l, r) = 0 if l > r; D(l, r) = piles[l] if l = r; and D(l, r) = max(piles[l] - D(l+1, r), piles[r] - D(l, r-1)) if l < r. Then D(0, n-1) is the final score difference (Alice minus Bob) under optimal play, and D(0, n-1) > 0; hence Alice ends with strictly more stones than Bob, so the returned Boolean true is correct.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_1 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    Aegis.StoneGame.stone_game piles = ok true ∧
      0 < D (vals piles) 0 ((vals piles).length - 1) ∧
      IsGameValue (vals piles) (D (vals piles) 0 ((vals piles).length - 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), Aegis.StoneGame.stone_game piles = ok true ∧
      0 < D (vals piles) 0 ((vals piles).length - 1) ∧
      IsGameValue (vals piles) (D (vals piles) 0 ((vals piles).length - 1))) := by
  sorry

/-- The function does not fail on the input: there exists a Boolean b such that the result is Result.ok b. In particular, no panic, out-of-bounds access, or 64-bit arithmetic overflow occurs.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_2 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    ∃ b : Bool, Aegis.StoneGame.stone_game piles = ok b := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), ∃ b : Bool, Aegis.StoneGame.stone_game piles = ok b) := by
  sorry

/-- Whenever the function returns Result.ok true, Alice has a winning strategy from the initial row: there exists a rule selecting one of the two end piles on each of Alice's turns such that, for every legal sequence of Bob's choices, Alice's final stone total is strictly greater than Bob's.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_3 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    Aegis.StoneGame.stone_game piles = ok true →
      ∃ σ : Strategy, ∀ τ : Strategy,
        (play σ τ (vals piles)).alice > (play σ τ (vals piles)).bob := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), Aegis.StoneGame.stone_game piles = ok true →
      ∃ σ : Strategy, ∀ τ : Strategy,
        (play σ τ (vals piles)).alice > (play σ τ (vals piles)).bob) := by
  sorry

/-- Whenever the function returns Result.ok true, at least one of Alice's two possible first moves is winning: either taking piles[0] gives final score difference piles[0] - D(1, n-1) > 0, or taking piles[n-1] gives final score difference piles[n-1] - D(0, n-2) > 0, where D(l, r) is the optimal current-player score difference from the interval piles[l..r] and D(l, r) = 0 when l > r.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_4 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    Aegis.StoneGame.stone_game piles = ok true →
      entry (vals piles) 0 - D (vals piles) 1 ((vals piles).length - 1) > 0 ∨
      entry (vals piles) ((vals piles).length - 1) - D (vals piles) 0 ((vals piles).length - 2) >
        0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), Aegis.StoneGame.stone_game piles = ok true →
      entry (vals piles) 0 - D (vals piles) 1 ((vals piles).length - 1) > 0 ∨
      entry (vals piles) ((vals piles).length - 1) - D (vals piles) 0 ((vals piles).length - 2) >
        0) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} piles[i], E = sum of piles[i] over even i with 0 <= i < n, and O = sum of piles[i] over odd i with 0 <= i < n. Whenever the function returns Result.ok true, Alice has a strategy that can collect exactly all even-indexed piles or exactly all odd-indexed piles; since S is odd, one of E and O is strictly greater than S/2, so choosing that parity class is a winning strategy for Alice.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_5 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    Aegis.StoneGame.stone_game piles = ok true →
      ((∃ σ : Strategy, ∀ τ : Strategy,
          (play σ τ (vals piles)).alice = sumEven (vals piles)) ∨
        (∃ σ : Strategy, ∀ τ : Strategy,
          (play σ τ (vals piles)).alice = sumOdd (vals piles))) ∧
      (sumEven (vals piles) > (vals piles).sum / 2 ∨
        sumOdd (vals piles) > (vals piles).sum / 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), Aegis.StoneGame.stone_game piles = ok true →
      ((∃ σ : Strategy, ∀ τ : Strategy,
          (play σ τ (vals piles)).alice = sumEven (vals piles)) ∨
        (∃ σ : Strategy, ∀ τ : Strategy,
          (play σ τ (vals piles)).alice = sumOdd (vals piles))) ∧
      (sumEven (vals piles) > (vals piles).sum / 2 ∨
        sumOdd (vals piles) > (vals piles).sum / 2)) := by
  sorry

/-- Let rev be the slice of length n = len(piles) with rev[i] = piles[n-1-i] for 0 <= i < n. If the function returns Result.ok b on piles and Result.ok b' on rev, then b = b'. Thus the Boolean answer is invariant under reversing the row.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_6 (piles rev : Slice Std.I64)
    (h_rev : vals rev = (vals piles).reverse)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    ∀ b b' : Bool, Aegis.StoneGame.stone_game piles = ok b →
      Aegis.StoneGame.stone_game rev = ok b' → b = b' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (piles rev : Slice Std.I64)
    (h_rev : vals rev = (vals piles).reverse)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), ∀ b b' : Bool, Aegis.StoneGame.stone_game piles = ok b →
      Aegis.StoneGame.stone_game rev = ok b' → b = b') := by
  sorry

/-- Let q be defined by q[i] = piles[i] + c for 0 <= i < n. If the function returns Result.ok b on piles and Result.ok b' on q, then b = b'. Thus adding the same integer to every pile, while keeping all piles in [1, 500], does not change the winner.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd; c is an integer such that 1 <= piles[i] + c <= 500 for every i. -/
theorem spec_7 (piles q : Slice Std.I64) (c : Int)
    (h_shift : vals q = (vals piles).map (fun v => v + c))
    (h_shift_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i + c ∧ entry (vals piles) i + c ≤ 500)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    ∀ b b' : Bool, Aegis.StoneGame.stone_game piles = ok b →
      Aegis.StoneGame.stone_game q = ok b' → b = b' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (piles q : Slice Std.I64) (c : Int)
    (h_shift : vals q = (vals piles).map (fun v => v + c))
    (h_shift_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i + c ∧ entry (vals piles) i + c ≤ 500)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), ∀ b b' : Bool, Aegis.StoneGame.stone_game piles = ok b →
      Aegis.StoneGame.stone_game q = ok b' → b = b') := by
  sorry

/-- Let q be defined by q[i] = k*piles[i] for 0 <= i < n. If the function returns Result.ok b on piles and Result.ok b' on q, then b = b'. Thus multiplying every pile by the same positive odd factor, while keeping all piles in [1, 500], does not change the winner.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd; k is a positive odd integer such that 1 <= k*piles[i] <= 500 for every i. -/
theorem spec_8 (piles q : Slice Std.I64) (k : Nat)
    (h_k_pos : 0 < k)
    (h_k_odd : k % 2 = 1)
    (h_scale : vals q = (vals piles).map (fun v => v * (k : Int)))
    (h_scale_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i * (k : Int) ∧ entry (vals piles) i * (k : Int) ≤ 500)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    ∀ b b' : Bool, Aegis.StoneGame.stone_game piles = ok b →
      Aegis.StoneGame.stone_game q = ok b' → b = b' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (piles q : Slice Std.I64) (k : Nat)
    (h_k_pos : 0 < k)
    (h_k_odd : k % 2 = 1)
    (h_scale : vals q = (vals piles).map (fun v => v * (k : Int)))
    (h_scale_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i * (k : Int) ∧ entry (vals piles) i * (k : Int) ≤ 500)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), ∀ b b' : Bool, Aegis.StoneGame.stone_game piles = ok b →
      Aegis.StoneGame.stone_game q = ok b' → b = b') := by
  sorry

/-- Whenever the function returns Result.ok true, let A be Alice's final stone total under optimal play and S = sum(piles). Then S/2 < A <= S. Equivalently, the optimal score difference D = 2*A - S satisfies 0 < D <= S.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_9 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    Aegis.StoneGame.stone_game piles = ok true →
      (vals piles).sum / 2 < aliceTotal (vals piles) ∧
        aliceTotal (vals piles) ≤ (vals piles).sum ∧
        0 < D (vals piles) 0 ((vals piles).length - 1) ∧
        D (vals piles) 0 ((vals piles).length - 1) ≤ (vals piles).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), Aegis.StoneGame.stone_game piles = ok true →
      (vals piles).sum / 2 < aliceTotal (vals piles) ∧
        aliceTotal (vals piles) ≤ (vals piles).sum ∧
        0 < D (vals piles) 0 ((vals piles).length - 1) ∧
        D (vals piles) 0 ((vals piles).length - 1) ≤ (vals piles).sum) := by
  sorry

/-- Whenever the function returns Result.ok true, Bob has no winning strategy: there is no rule for Bob's choices such that, against every legal Alice strategy, Bob's final stone total is strictly greater than Alice's.
  Preconditions: len(piles) is even; 2 <= len(piles) <= 500; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 500; the sum S = sum_{i=0}^{len(piles)-1} piles[i] is odd. -/
theorem spec_10 (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum) :
    Aegis.StoneGame.stone_game piles = ok true →
      ¬ (∃ τ : Strategy, ∀ σ : Strategy,
          (play σ τ (vals piles)).bob > (play σ τ (vals piles)).alice) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (piles : Slice Std.I64)
    (h_len_even : (vals piles).length % 2 = 0)
    (h_len_range : 2 ≤ (vals piles).length ∧ (vals piles).length ≤ 500)
    (h_bounds : ∀ i, i < (vals piles).length →
      1 ≤ entry (vals piles) i ∧ entry (vals piles) i ≤ 500)
    (h_sum_odd : Odd (vals piles).sum), Aegis.StoneGame.stone_game piles = ok true →
      ¬ (∃ τ : Strategy, ∀ σ : Strategy,
          (play σ τ (vals piles)).bob > (play σ τ (vals piles)).alice)) := by
  sorry

end AegisSpec.StoneGame
