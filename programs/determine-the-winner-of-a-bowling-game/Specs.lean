import Aegis.IsWinner.Code.Funs

/-!
# Specifications of `Aegis.IsWinner.is_winner`

LeetCode problem `determine-the-winner-of-a-bowling-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsWinner

def weight (xs : List Std.I64) (i : ℕ) : ℤ :=
  if (1 ≤ i ∧ (xs[i - 1]?).map (fun x => x.val) = some 10) ∨
      (2 ≤ i ∧ (xs[i - 2]?).map (fun x => x.val) = some 10) then
    2
  else
    1

def score (xs : List Std.I64) : ℤ :=
  (xs.mapIdx (fun i x => x.val * weight xs i)).sum

/-- Let score(xs) for a slice xs of length n be sum_{i=0}^{n-1} xs[i] * m_i, where m_i = 2 if (i >= 1 and xs[i-1] = 10) or (i >= 2 and xs[i-2] = 10), and m_i = 1 otherwise. For every valid input, the function returns a result r and: r = 1 if score(player1) > score(player2), r = 2 if score(player2) > score(player1), and r = 0 if score(player1) = score(player2).
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_1
    (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10) :
    ∃ r, Aegis.IsWinner.is_winner player1 player2 = ok r ∧
      (score player1.val > score player2.val → r.val = 1) ∧
      (score player2.val > score player1.val → r.val = 2) ∧
      (score player1.val = score player2.val → r.val = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10), ∃ r, Aegis.IsWinner.is_winner player1 player2 = ok r ∧
      (score player1.val > score player2.val → r.val = 1) ∧
      (score player2.val > score player1.val → r.val = 2) ∧
      (score player1.val = score player2.val → r.val = 0)) := by
  sorry

/-- For every valid input, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_2
    (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10) :
    ∃ r, Aegis.IsWinner.is_winner player1 player2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10), ∃ r, Aegis.IsWinner.is_winner player1 player2 = ok r) := by
  sorry

/-- Whenever the function returns a result r on a valid input, r = 0 or r = 1 or r = 2.
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_3
    (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (r : Std.I64) (hr : Aegis.IsWinner.is_winner player1 player2 = ok r) :
    r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (r : Std.I64) (hr : Aegis.IsWinner.is_winner player1 player2 = ok r), r.val = 0 ∨ r.val = 1 ∨ r.val = 2) := by
  sorry

/-- Let score(xs) for a slice xs of length n be sum_{i=0}^{n-1} xs[i] * m_i, where m_i = 2 if (i >= 1 and xs[i-1] = 10) or (i >= 2 and xs[i-2] = 10), and m_i = 1 otherwise. Whenever the function returns a result r, r = 0 if and only if score(player1) = score(player2).
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_4
    (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (r : Std.I64) (hr : Aegis.IsWinner.is_winner player1 player2 = ok r) :
    (r.val = 0 ↔ score player1.val = score player2.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (r : Std.I64) (hr : Aegis.IsWinner.is_winner player1 player2 = ok r), (r.val = 0 ↔ score player1.val = score player2.val)) := by
  sorry

/-- Let r be the result returned on (player1, player2) and let r' be the result returned on (player2, player1). Whenever both calls return results, the following holds: if r = 0 then r' = 0; if r = 1 then r' = 2; if r = 2 then r' = 1.
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_5
    (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (r r' : Std.I64)
    (hr : Aegis.IsWinner.is_winner player1 player2 = ok r)
    (hr' : Aegis.IsWinner.is_winner player2 player1 = ok r') :
    (r.val = 0 → r'.val = 0) ∧ (r.val = 1 → r'.val = 2) ∧ (r.val = 2 → r'.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (player1 player2 : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (r r' : Std.I64)
    (hr : Aegis.IsWinner.is_winner player1 player2 = ok r)
    (hr' : Aegis.IsWinner.is_winner player2 player1 = ok r'), (r.val = 0 → r'.val = 0) ∧ (r.val = 1 → r'.val = 2) ∧ (r.val = 2 → r'.val = 1)) := by
  sorry

/-- For any slice player1' of length n with 0 <= player1'[i] <= 10 for every i and player1'[i] >= player1[i] for every i, let r be the result returned on (player1, player2) and r' the result returned on (player1', player2). Whenever both calls return results, if r = 1 then r' = 1.
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_6
    (player1 player2 player1' : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (h1' : player1'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (hb1' : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1'.val[i]'(by omega)).val ∧ (player1'.val[i]'(by omega)).val ≤ 10)
    (hmono : ∀ (i : ℕ) (hi : i < n),
      (player1.val[i]'(by omega)).val ≤ (player1'.val[i]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.IsWinner.is_winner player1 player2 = ok r)
    (hr' : Aegis.IsWinner.is_winner player1' player2 = ok r')
    (hr1 : r.val = 1) :
    r'.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (player1 player2 player1' : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (h1' : player1'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (hb1' : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1'.val[i]'(by omega)).val ∧ (player1'.val[i]'(by omega)).val ≤ 10)
    (hmono : ∀ (i : ℕ) (hi : i < n),
      (player1.val[i]'(by omega)).val ≤ (player1'.val[i]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.IsWinner.is_winner player1 player2 = ok r)
    (hr' : Aegis.IsWinner.is_winner player1' player2 = ok r')
    (hr1 : r.val = 1), r'.val = 1) := by
  sorry

/-- For any slice player2' of length n with 0 <= player2'[i] <= 10 for every i and player2'[i] >= player2[i] for every i, let r be the result returned on (player1, player2) and r' the result returned on (player1, player2'). Whenever both calls return results, if r = 2 then r' = 2.
  Preconditions: len(player1) = len(player2) = n, 1 <= n <= 1000, and for every i with 0 <= i < n, 0 <= player1[i] <= 10 and 0 <= player2[i] <= 10. -/
theorem spec_7
    (player1 player2 player2' : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (h2' : player2'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (hb2' : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2'.val[i]'(by omega)).val ∧ (player2'.val[i]'(by omega)).val ≤ 10)
    (hmono : ∀ (i : ℕ) (hi : i < n),
      (player2.val[i]'(by omega)).val ≤ (player2'.val[i]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.IsWinner.is_winner player1 player2 = ok r)
    (hr' : Aegis.IsWinner.is_winner player1 player2' = ok r')
    (hr1 : r.val = 2) :
    r'.val = 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (player1 player2 player2' : Slice Std.I64) (n : ℕ)
    (h1 : player1.val.length = n) (h2 : player2.val.length = n)
    (h2' : player2'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hb1 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player1.val[i]'(by omega)).val ∧ (player1.val[i]'(by omega)).val ≤ 10)
    (hb2 : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2.val[i]'(by omega)).val ∧ (player2.val[i]'(by omega)).val ≤ 10)
    (hb2' : ∀ (i : ℕ) (hi : i < n),
      0 ≤ (player2'.val[i]'(by omega)).val ∧ (player2'.val[i]'(by omega)).val ≤ 10)
    (hmono : ∀ (i : ℕ) (hi : i < n),
      (player2.val[i]'(by omega)).val ≤ (player2'.val[i]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.IsWinner.is_winner player1 player2 = ok r)
    (hr' : Aegis.IsWinner.is_winner player1 player2' = ok r')
    (hr1 : r.val = 2), r'.val = 2) := by
  sorry

end AegisSpec.IsWinner
