import Aegis.WinningPlayerCount.Code.Funs

/-!
# Specifications of `Aegis.WinningPlayerCount.winning_player_count`

LeetCode problem `find-the-number-of-winning-players`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.WinningPlayerCount

def rowValue (v : alloc.vec.Vec I64) : List ℤ :=
  v.val.map (fun x => x.val)

def rowValues (pick : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  pick.val.map rowValue

def pickRow (pick : Slice (alloc.vec.Vec I64)) (j : ℕ) : List ℤ :=
  ((rowValues pick)[j]?).getD []

def countPair (pick : Slice (alloc.vec.Vec I64)) (i c : ℤ) : ℕ :=
  (rowValues pick).countP (fun r => decide (r[0]? = some i ∧ r[1]? = some c))

def countPlayer (pick : Slice (alloc.vec.Vec I64)) (i : ℤ) : ℕ :=
  (rowValues pick).countP (fun r => decide (r[0]? = some i))

def playerWins (pick : Slice (alloc.vec.Vec I64)) (i : ℤ) : Bool :=
  (List.range 11).any fun c => decide (i < ((countPair pick i (c : ℤ) : ℕ) : ℤ))

def winCount (n : ℤ) (pick : Slice (alloc.vec.Vec I64)) : ℕ :=
  (List.range n.toNat).countP fun x => playerWins pick (x : ℤ)

def pickedPlayerCount (n : ℤ) (pick : Slice (alloc.vec.Vec I64)) : ℕ :=
  (List.range n.toNat).countP fun x => decide (0 < countPlayer pick (x : ℤ))

def enoughPicksCount (n : ℤ) (pick : Slice (alloc.vec.Vec I64)) : ℕ :=
  (List.range n.toNat).countP fun x =>
    decide (((x : ℤ) + 1 ≤ ((countPlayer pick (x : ℤ) : ℕ) : ℤ)))

def IsPermutationOf (pick' pick : Slice (alloc.vec.Vec I64)) : Prop :=
  pick'.val.length = pick.val.length ∧
    ∃ pi : ℕ → ℕ,
      (∀ j, j < pick.val.length → pi j < pick.val.length) ∧
      (∀ j, j < pick.val.length → ∃ k, k < pick.val.length ∧ pi k = j) ∧
      (∀ j, j < pick.val.length → pick'.val[j]? = pick.val[pi j]?)

/-- Whenever the function returns a result r, r equals the number of integers i with 0 <= i < n for which there exists an integer c with 0 <= c <= 10 such that #{j | 0 <= j < len(pick) and pick[j][0] = i and pick[j][1] = c} > i.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_1 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val = (winCount n pick : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val = (winCount n pick : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_2 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      0 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      0 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_3 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∃ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∃ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every integer i with 0 <= i < n and every integer c with 0 <= c <= 10, #{j | 0 <= j < len(pick) and pick[j][0] = i and pick[j][1] = c} <= i.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_4 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      (r.val = 0 ↔
        ∀ i : ℤ, 0 ≤ i → i < n.val →
          ∀ c : ℤ, 0 ≤ c → c ≤ 10 →
            ((countPair pick i c : ℕ) : ℤ) ≤ i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      (r.val = 0 ↔
        ∀ i : ℤ, 0 ≤ i → i < n.val →
          ∀ c : ℤ, 0 ≤ c → c ≤ 10 →
            ((countPair pick i c : ℕ) : ℤ) ≤ i)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if for every integer i with 0 <= i < n there exists an integer c with 0 <= c <= 10 such that #{j | 0 <= j < len(pick) and pick[j][0] = i and pick[j][1] = c} > i.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_5 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      (r.val = n.val ↔
        ∀ i : ℤ, 0 ≤ i → i < n.val →
          ∃ c : ℤ, 0 ≤ c ∧ c ≤ 10 ∧
            i < ((countPair pick i c : ℕ) : ℤ)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      (r.val = n.val ↔
        ∀ i : ℤ, 0 ≤ i → i < n.val →
          ∃ c : ℤ, 0 ≤ c ∧ c ≤ 10 ∧
            i < ((countPair pick i c : ℕ) : ℤ))) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exist integers i and c with 0 <= i < n and 0 <= c <= 10 such that #{j | 0 <= j < len(pick) and pick[j][0] = i and pick[j][1] = c} > i.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_6 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      0 < r.val →
        ∃ i c : ℤ, 0 ≤ i ∧ i < n.val ∧ 0 ≤ c ∧ c ≤ 10 ∧
          i < ((countPair pick i c : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      0 < r.val →
        ∃ i c : ℤ, 0 ≤ i ∧ i < n.val ∧ 0 ≤ c ∧ c ≤ 10 ∧
          i < ((countPair pick i c : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r and r < n, there exists an integer i with 0 <= i < n such that for every integer c with 0 <= c <= 10, #{j | 0 <= j < len(pick) and pick[j][0] = i and pick[j][1] = c} <= i.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_7 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val < n.val →
        ∃ i : ℤ, 0 ≤ i ∧ i < n.val ∧
          ∀ c : ℤ, 0 ≤ c → c ≤ 10 →
            ((countPair pick i c : ℕ) : ℤ) ≤ i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val < n.val →
        ∃ i : ℤ, 0 ≤ i ∧ i < n.val ∧
          ∀ c : ℤ, 0 ≤ c → c ≤ 10 →
            ((countPair pick i c : ℕ) : ℤ) ≤ i) := by
  sorry

/-- Let pick' be the list obtained by appending the pair [x,y] to pick. Whenever the function returns r on input (n,pick) and r' on input (n,pick'), r' >= r.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 99; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10; 0 <= x <= n - 1; 0 <= y <= 10. -/
theorem spec_8 (n : I64) (pick pick' : Slice (alloc.vec.Vec I64))
    (v : alloc.vec.Vec I64) (x y : I64)
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 99)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10)
    (h_x_lower : 0 ≤ x.val) (h_x_upper : x.val ≤ n.val - 1)
    (h_y_lower : 0 ≤ y.val) (h_y_upper : y.val ≤ 10)
    (h_v : rowValue v = [x.val, y.val])
    (h_pick' : pick'.val = pick.val ++ [v]) :
    ∀ r r' : I64,
      Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      Aegis.WinningPlayerCount.winning_player_count n pick' = ok r' →
        r.val ≤ r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (pick pick' : Slice (alloc.vec.Vec I64))
    (v : alloc.vec.Vec I64) (x y : I64)
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 99)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10)
    (h_x_lower : 0 ≤ x.val) (h_x_upper : x.val ≤ n.val - 1)
    (h_y_lower : 0 ≤ y.val) (h_y_upper : y.val ≤ 10)
    (h_v : rowValue v = [x.val, y.val])
    (h_pick' : pick'.val = pick.val ++ [v]), ∀ r r' : I64,
      Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      Aegis.WinningPlayerCount.winning_player_count n pick' = ok r' →
        r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns r on input (n,pick) and r' on input (n,pick'), r = r'.
  Preconditions: 2 <= n <= 10; both pick and pick' are lists of pairs satisfying 1 <= len <= 100, each pair has length 2, 0 <= pair[0] <= n - 1, and 0 <= pair[1] <= 10; pick' is a permutation of pick, meaning len(pick') = len(pick) and there is a bijection pi from indices 0 <= j < len(pick) onto the same index range with pick'[j] = pick[pi(j)] for every j. -/
theorem spec_9 (n : I64) (pick pick' : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10)
    (h_len_lower' : 1 ≤ pick'.val.length) (h_len_upper' : pick'.val.length ≤ 100)
    (h_row_len' : ∀ j, j < pick'.val.length → (pickRow pick' j).length = 2)
    (h_player' : ∀ j, j < pick'.val.length →
      0 ≤ (pickRow pick' j)[0]! ∧ (pickRow pick' j)[0]! ≤ n.val - 1)
    (h_color' : ∀ j, j < pick'.val.length →
      0 ≤ (pickRow pick' j)[1]! ∧ (pickRow pick' j)[1]! ≤ 10)
    (h_perm : IsPermutationOf pick' pick) :
    ∀ r r' : I64,
      Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      Aegis.WinningPlayerCount.winning_player_count n pick' = ok r' →
        r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (pick pick' : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10)
    (h_len_lower' : 1 ≤ pick'.val.length) (h_len_upper' : pick'.val.length ≤ 100)
    (h_row_len' : ∀ j, j < pick'.val.length → (pickRow pick' j).length = 2)
    (h_player' : ∀ j, j < pick'.val.length →
      0 ≤ (pickRow pick' j)[0]! ∧ (pickRow pick' j)[0]! ≤ n.val - 1)
    (h_color' : ∀ j, j < pick'.val.length →
      0 ≤ (pickRow pick' j)[1]! ∧ (pickRow pick' j)[1]! ≤ 10)
    (h_perm : IsPermutationOf pick' pick), ∀ r r' : I64,
      Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      Aegis.WinningPlayerCount.winning_player_count n pick' = ok r' →
        r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on input (n,pick) and r' on input (n',pick), r' = r.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10; n' is an integer with n <= n' <= 10. -/
theorem spec_10 (n n' : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10)
    (h_n'_lower : n.val ≤ n'.val) (h_n'_upper : n'.val ≤ 10) :
    ∀ r r' : I64,
      Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      Aegis.WinningPlayerCount.winning_player_count n' pick = ok r' →
        r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n n' : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10)
    (h_n'_lower : n.val ≤ n'.val) (h_n'_upper : n'.val ≤ 10), ∀ r r' : I64,
      Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      Aegis.WinningPlayerCount.winning_player_count n' pick = ok r' →
        r'.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(pick).
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_11 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val ≤ ((pick.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val ≤ ((pick.val.length : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r <= #{x | 0 <= x < n and there exists j with 0 <= j < len(pick) and pick[j][0] = x}.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_12 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val ≤ ((pickedPlayerCount n pick : ℕ) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      r.val ≤ ((pickedPlayerCount n pick : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every integer i with 0 <= i < n, if there exists an integer c with 0 <= c <= 10 such that #{j | 0 <= j < len(pick) and pick[j][0] = i and pick[j][1] = c} > i, then #{j | 0 <= j < len(pick) and pick[j][0] = i} >= i + 1; consequently r <= #{i | 0 <= i < n and #{j | 0 <= j < len(pick) and pick[j][0] = i} >= i + 1}.
  Preconditions: 2 <= n <= 10; 1 <= len(pick) <= 100; for every j with 0 <= j < len(pick), len(pick[j]) = 2, 0 <= pick[j][0] <= n - 1, and 0 <= pick[j][1] <= 10. -/
theorem spec_13 (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10) :
    ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      (∀ i : ℤ, 0 ≤ i → i < n.val →
        (∃ c : ℤ, 0 ≤ c ∧ c ≤ 10 ∧
          i < ((countPair pick i c : ℕ) : ℤ)) →
        i + 1 ≤ ((countPlayer pick i : ℕ) : ℤ)) ∧
      r.val ≤ ((enoughPicksCount n pick : ℕ) : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (pick : Slice (alloc.vec.Vec I64))
    (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 10)
    (h_len_lower : 1 ≤ pick.val.length) (h_len_upper : pick.val.length ≤ 100)
    (h_row_len : ∀ j, j < pick.val.length → (pickRow pick j).length = 2)
    (h_player : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[0]! ∧ (pickRow pick j)[0]! ≤ n.val - 1)
    (h_color : ∀ j, j < pick.val.length →
      0 ≤ (pickRow pick j)[1]! ∧ (pickRow pick j)[1]! ≤ 10), ∀ r : I64, Aegis.WinningPlayerCount.winning_player_count n pick = ok r →
      (∀ i : ℤ, 0 ≤ i → i < n.val →
        (∃ c : ℤ, 0 ≤ c ∧ c ≤ 10 ∧
          i < ((countPair pick i c : ℕ) : ℤ)) →
        i + 1 ≤ ((countPlayer pick i : ℕ) : ℤ)) ∧
      r.val ≤ ((enoughPicksCount n pick : ℕ) : ℤ)) := by
  sorry

end AegisSpec.WinningPlayerCount
