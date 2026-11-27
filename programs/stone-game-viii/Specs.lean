import Aegis.StoneGameViii.Code.Funs

/-!
# Specifications of `Aegis.StoneGameViii.stone_game_viii`

LeetCode problem `stone-game-viii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.StoneGameViii

def P (s : List I64) (m : Nat) : Int := ((s.take m).map (fun x => x.val)).sum

def absSum (s : List I64) : Nat := (s.map (fun x => x.val.natAbs)).sum

noncomputable def Fut (s : List I64) (n : Nat) (m : Nat) : Int :=
  Nat.strongRecOn m (fun m ih =>
    if h : m = 0 then 0
    else
      (Finset.range m).attach.sup' ⟨⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero h)⟩, by simp⟩
        (fun t => P s (n - t.val) - ih t.val (Finset.mem_range.mp t.property)))

@[simp]
theorem Fut_zero (s : List I64) (n : Nat) : Fut s n 0 = 0 := by
  rw [Fut, Nat.strongRecOn_eq]
  simp

theorem Fut_succ (s : List I64) (n m : Nat) :
    Fut s n (m + 1) =
      (Finset.range (m + 1)).attach.sup' ⟨⟨0, by simp⟩, by simp⟩
        (fun t => P s (n - t.val) - Fut s n t.val) := by
  rw [Fut, Nat.strongRecOn_eq]
  congr 2 with t

noncomputable def F (s : List I64) (k : Nat) : Int := Fut s s.length (s.length - k)

def U (s : List I64) : Int :=
  if h : 2 ≤ s.length then
    max (P s s.length)
      ((Finset.Icc 2 s.length).sup' ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
        (fun j => P s j - P s s.length))
  else P s s.length

def dpBackward (s : List I64) : Nat → Int → Int
  | 0, dp => dp
  | (m + 1), dp => dpBackward s m (max dp (P s (m + 2) - dp))

/-- Define P(m) = sum_{i=0}^{m-1} stones[i] for 0 <= m <= n. Define F(n) = 0 and, for 1 <= k < n, F(k) = max{ P(j) - F(j) | k < j <= n }, where the maximum is over the nonempty finite set {k+1, ..., n}. The function returns a result r and r = F(1). Here F(k) is the optimal future score difference, current player minus opponent, when the first k original stones have already been merged into the single leftmost stone and it is the current player's turn; the initial Alice position corresponds to F(1) because Alice's first move must choose some j with 2 <= j <= n.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_1 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧ r.val = F stones.val 1 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧ r.val = F stones.val 1) := by
  sorry

/-- The function returns a result r; it does not fail, panic, go out of bounds, or overflow for any input satisfying the preconditions.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_2 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r) := by
  sorry

/-- Let A = sum_{i=0}^{n-1} |stones[i]|. Whenever the function returns r, |r| <= A.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_3 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r → r.val.natAbs ≤ absSum stones.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r → r.val.natAbs ≤ absSum stones.val) := by
  sorry

/-- Let T = sum_{i=0}^{n-1} stones[i]. Whenever the function returns r, r >= T.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_4 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∀ r : I64,
      Aegis.StoneGameViii.stone_game_viii stones = ok r → r.val ≥ P stones.val stones.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∀ r : I64,
      Aegis.StoneGameViii.stone_game_viii stones = ok r → r.val ≥ P stones.val stones.val.length) := by
  sorry

/-- Whenever the function returns r, r >= -stones[n-1].
  Preconditions: Let n = len(stones). 3 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_5 (stones : Slice I64)
    (hn : 3 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      r.val ≥ -(stones.val[stones.val.length - 1]'(by omega)).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 3 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      r.val ≥ -(stones.val[stones.val.length - 1]'(by omega)).val) := by
  sorry

/-- Let P(m) = sum_{i=0}^{m-1} stones[i] for 0 <= m <= n, and let U = max( P(n), max_{2 <= j <= n} (P(j) - P(n)) ). Whenever the function returns r, r <= U.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_6 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r → r.val ≤ U stones.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r → r.val ≤ U stones.val) := by
  sorry

/-- The function returns r = stones[0] + stones[1].
  Preconditions: len(stones) = 2 and for i = 0,1, -10000 <= stones[i] <= 10000. -/
theorem spec_7 (stones : Slice I64)
    (hn : stones.val.length = 2)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = (stones.val[0]'(by omega)).val + (stones.val[1]'(by omega)).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : stones.val.length = 2)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = (stones.val[0]'(by omega)).val + (stones.val[1]'(by omega)).val) := by
  sorry

/-- Let T = stones[0] + stones[1] + stones[2] and let P2 = stones[0] + stones[1]. The function returns r = max(T, P2 - T) = max(T, -stones[2]).
  Preconditions: len(stones) = 3 and for i = 0,1,2, -10000 <= stones[i] <= 10000. -/
theorem spec_8 (stones : Slice I64)
    (hn : stones.val.length = 3)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = max (P stones.val 3) (P stones.val 2 - P stones.val 3) ∧
      r.val = max (P stones.val 3) (-(stones.val[2]'(by omega)).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : stones.val.length = 3)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = max (P stones.val 3) (P stones.val 2 - P stones.val 3) ∧
      r.val = max (P stones.val 3) (-(stones.val[2]'(by omega)).val)) := by
  sorry

/-- The function returns r = -stones[n-1].
  Preconditions: Let n = len(stones). 3 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 0. -/
theorem spec_9 (stones : Slice I64)
    (hn : 3 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 0) :
    ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = -(stones.val[stones.val.length - 1]'(by omega)).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 3 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 0), ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = -(stones.val[stones.val.length - 1]'(by omega)).val) := by
  sorry

/-- The function returns r = P(n).
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. Let P(m) = sum_{i=0}^{m-1} stones[i] for 0 <= m <= n. Assume P(n) >= 0 and, for every j with 2 <= j <= n, P(j) <= P(n). -/
theorem spec_10 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000)
    (hPn : 0 ≤ P stones.val stones.val.length)
    (hmono : ∀ j : Nat, 2 ≤ j → j ≤ stones.val.length →
      P stones.val j ≤ P stones.val stones.val.length) :
    ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = P stones.val stones.val.length := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000)
    (hPn : 0 ≤ P stones.val stones.val.length)
    (hmono : ∀ j : Nat, 2 ≤ j → j ≤ stones.val.length →
      P stones.val j ≤ P stones.val stones.val.length), ∃ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r ∧
      r.val = P stones.val stones.val.length) := by
  sorry

/-- If stone_game_viii(stones) returns r and stone_game_viii(stones2) returns r2, then r2 = c * r.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. Let c be an integer with c >= 0, and let stones2 be a slice of length n such that stones2[i] = c * stones[i] for every i, with each product represented as an i64 value. -/
theorem spec_11 (stones stones2 : Slice I64) (c : Int)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000)
    (hc : 0 ≤ c)
    (hlen : stones2.val.length = stones.val.length)
    (hrel : ∀ (i : Nat) (h1 : i < stones.val.length) (h2 : i < stones2.val.length),
      (stones2.val[i]'h2).val = c * (stones.val[i]'h1).val) :
    ∀ r r2 : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      Aegis.StoneGameViii.stone_game_viii stones2 = ok r2 → r2.val = c * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (stones stones2 : Slice I64) (c : Int)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000)
    (hc : 0 ≤ c)
    (hlen : stones2.val.length = stones.val.length)
    (hrel : ∀ (i : Nat) (h1 : i < stones.val.length) (h2 : i < stones2.val.length),
      (stones2.val[i]'h2).val = c * (stones.val[i]'h1).val), ∀ r r2 : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      Aegis.StoneGameViii.stone_game_viii stones2 = ok r2 → r2.val = c * r.val) := by
  sorry

/-- Let P(m) = sum_{i=0}^{m-1} stones[i] for 0 <= m <= n. If the function returns r, then there exist an integer m >= 1 and integers k_1, ..., k_m such that 2 <= k_1 < k_2 < ... < k_m = n and r = sum_{t=1}^{m} (-1)^{t+1} P(k_t).
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. -/
theorem spec_12 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      ∃ (m : Nat) (hm : 1 ≤ m) (k : Fin m → Nat),
        (∀ t : Fin m, 2 ≤ k t) ∧
        (∀ t u : Fin m, t < u → k t < k u) ∧
        k ⟨m - 1, by omega⟩ = stones.val.length ∧
        r.val = ∑ t : Fin m, (-1 : Int) ^ t.val * P stones.val (k t) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), ∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      ∃ (m : Nat) (hm : 1 ≤ m) (k : Fin m → Nat),
        (∀ t : Fin m, 2 ≤ k t) ∧
        (∀ t u : Fin m, t < u → k t < k u) ∧
        k ⟨m - 1, by omega⟩ = stones.val.length ∧
        r.val = ∑ t : Fin m, (-1 : Int) ^ t.val * P stones.val (k t)) := by
  sorry

/-- Then F(n-1) = P(n), and for every k with 1 <= k <= n-2, F(k) = max(F(k+1), P(k+1) - F(k+1)). Equivalently, the value can be computed backward from dp = P(n), updating dp := max(dp, P(k+1)-dp) for k = n-2, n-3, ..., 1, and returning the final dp.
  Preconditions: Let n = len(stones). 2 <= n <= 100000 and for every i with 0 <= i < n, -10000 <= stones[i] <= 10000. Let P(m) = sum_{i=0}^{m-1} stones[i] for 0 <= m <= n. Define F(n) = 0 and, for 1 <= k < n, F(k) = max{ P(j) - F(j) | k < j <= n }. -/
theorem spec_13 (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000) :
    F stones.val (stones.val.length - 1) = P stones.val stones.val.length ∧
    (∀ k : Nat, 1 ≤ k → k ≤ stones.val.length - 2 →
      F stones.val k = max (F stones.val (k + 1))
        (P stones.val (k + 1) - F stones.val (k + 1))) ∧
    (∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      r.val = dpBackward stones.val (stones.val.length - 2)
        (P stones.val stones.val.length)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (stones : Slice I64)
    (hn : 2 ≤ stones.val.length) (hnle : stones.val.length ≤ 100000)
    (hbound : ∀ i : Fin stones.val.length,
      -10000 ≤ (stones.val.get i).val ∧ (stones.val.get i).val ≤ 10000), F stones.val (stones.val.length - 1) = P stones.val stones.val.length ∧
    (∀ k : Nat, 1 ≤ k → k ≤ stones.val.length - 2 →
      F stones.val k = max (F stones.val (k + 1))
        (P stones.val (k + 1) - F stones.val (k + 1))) ∧
    (∀ r : I64, Aegis.StoneGameViii.stone_game_viii stones = ok r →
      r.val = dpBackward stones.val (stones.val.length - 2)
        (P stones.val stones.val.length))) := by
  sorry

end AegisSpec.StoneGameViii
