import Aegis.StoneGameIi.Code.Funs

/-!
# Specifications of `Aegis.StoneGameIi.stone_game_ii`

LeetCode problem `stone-game-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.StoneGameIi

  namespace AegisSpec.StoneGameIi

  def pvals (piles : Slice Std.I64) : List ℤ := piles.val.map (fun p => p.val)

  def suffixSum (l : List ℤ) (i : Nat) : ℤ := (l.drop i).sum

  def Vf (l : List ℤ) : Nat → Nat → Nat → ℤ
    | 0, _, _ => 0
    | fuel + 1, i, M =>
      if i ≥ l.length then 0
      else
        (List.range (Nat.min (2 * M) (l.length - i))).foldr
          (fun k acc =>
            max (suffixSum l i - Vf l fuel (i + k + 1) (Nat.max M (k + 1))) acc)
          (suffixSum l i - Vf l fuel (i + 1) (Nat.max M 1))

  def V (l : List ℤ) (i M : Nat) : ℤ := Vf l l.length i M

  /-- The function returns a result r such that r = V(0, 1), where V is defined for any integer i with 0 <= i <= len(piles) and any integer M >= 1 by: V(i, M) = 0 if i >= len(piles); otherwise V(i, M) = max_{1 <= X <= 2M, i+X <= len(piles)} ( total(i) - V(i+X, max(M, X)) ), where total(i) = sum_{j=i}^{len(piles)-1} piles[j] (and total(len(piles)) = 0).
    Preconditions: len(piles) >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_1 (piles : Slice Std.I64)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val = V (pvals piles) 0 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (piles : Slice Std.I64)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val = V (pvals piles) 0 1) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result r (i.e., it does not fail, panic, or overflow).
    Preconditions: len(piles) >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_2 (piles : Slice Std.I64)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (piles : Slice Std.I64)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r) := by
    sorry

  /-- The function returns a result r and r >= sum_{i=0}^{min(2, len(piles))-1} piles[i].
    Preconditions: len(piles) >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_3 (piles : Slice Std.I64)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧
        ((pvals piles).take (Nat.min 2 (pvals piles).length)).sum ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (piles : Slice Std.I64)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧
          ((pvals piles).take (Nat.min 2 (pvals piles).length)).sum ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{len(piles)-1} piles[i].
    Preconditions: len(piles) >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_4 (piles : Slice Std.I64)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val ≤ (pvals piles).sum := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (piles : Slice Std.I64)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val ≤ (pvals piles).sum) := by
    sorry

  /-- The function returns a result r and r = piles[0].
    Preconditions: len(piles) = 1; 1 <= piles[0] <= 10000. -/
  theorem spec_5 (piles : Slice Std.I64) (p0 : Std.I64)
      (hlen : piles.val.length = 1)
      (hpiles : piles.val = [p0])
      (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val = p0.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 : Std.I64)
        (hlen : piles.val.length = 1)
        (hpiles : piles.val = [p0])
        (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val = p0.val) := by
    sorry

  /-- The function returns a result r and r = piles[0] + piles[1].
    Preconditions: len(piles) = 2; 1 <= piles[0] <= 10000; 1 <= piles[1] <= 10000. -/
  theorem spec_6 (piles : Slice Std.I64) (p0 p1 : Std.I64)
      (hlen : piles.val.length = 2)
      (hpiles : piles.val = [p0, p1])
      (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
      (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val = p0.val + p1.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 : Std.I64)
        (hlen : piles.val.length = 2)
        (hpiles : piles.val = [p0, p1])
        (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
        (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val = p0.val + p1.val) := by
    sorry

  /-- The function returns a result r and r = piles[0] + max(piles[1], piles[3]).
    Preconditions: len(piles) = 4; 1 <= piles[i] <= 10000 for i=0,1,2,3. -/
  theorem spec_7 (piles : Slice Std.I64) (p0 p1 p2 p3 : Std.I64)
      (hlen : piles.val.length = 4)
      (hpiles : piles.val = [p0, p1, p2, p3])
      (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
      (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000)
      (hb2 : 1 ≤ p2.val ∧ p2.val ≤ 10000)
      (hb3 : 1 ≤ p3.val ∧ p3.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val = p0.val + max p1.val p3.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 p2 p3 : Std.I64)
        (hlen : piles.val.length = 4)
        (hpiles : piles.val = [p0, p1, p2, p3])
        (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
        (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000)
        (hb2 : 1 ≤ p2.val ∧ p2.val ≤ 10000)
        (hb3 : 1 ≤ p3.val ∧ p3.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val = p0.val + max p1.val p3.val) := by
    sorry

  /-- The function returns a result r and r = piles[0] + max(piles[1], piles[3] + min(piles[2], piles[4])).
    Preconditions: len(piles) = 5; 1 <= piles[i] <= 10000 for i=0,1,2,3,4. -/
  theorem spec_8 (piles : Slice Std.I64) (p0 p1 p2 p3 p4 : Std.I64)
      (hlen : piles.val.length = 5)
      (hpiles : piles.val = [p0, p1, p2, p3, p4])
      (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
      (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000)
      (hb2 : 1 ≤ p2.val ∧ p2.val ≤ 10000)
      (hb3 : 1 ≤ p3.val ∧ p3.val ≤ 10000)
      (hb4 : 1 ≤ p4.val ∧ p4.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧
        r.val = p0.val + max p1.val (p3.val + min p2.val p4.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 p2 p3 p4 : Std.I64)
        (hlen : piles.val.length = 5)
        (hpiles : piles.val = [p0, p1, p2, p3, p4])
        (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
        (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000)
        (hb2 : 1 ≤ p2.val ∧ p2.val ≤ 10000)
        (hb3 : 1 ≤ p3.val ∧ p3.val ≤ 10000)
        (hb4 : 1 ≤ p4.val ∧ p4.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧
          r.val = p0.val + max p1.val (p3.val + min p2.val p4.val)) := by
    sorry

  /-- The function returns a result r and r = max( piles[0] + piles[1], (if piles[2] >= piles[4] + min(piles[3], piles[5]) then piles[0] + piles[3] + piles[4] + piles[5] else piles[0] + piles[2] + max(piles[3], piles[5])) ).
    Preconditions: len(piles) = 6; 1 <= piles[i] <= 10000 for i=0,1,2,3,4,5. -/
  theorem spec_9 (piles : Slice Std.I64) (p0 p1 p2 p3 p4 p5 : Std.I64)
      (hlen : piles.val.length = 6)
      (hpiles : piles.val = [p0, p1, p2, p3, p4, p5])
      (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
      (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000)
      (hb2 : 1 ≤ p2.val ∧ p2.val ≤ 10000)
      (hb3 : 1 ≤ p3.val ∧ p3.val ≤ 10000)
      (hb4 : 1 ≤ p4.val ∧ p4.val ≤ 10000)
      (hb5 : 1 ≤ p5.val ∧ p5.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧
        r.val = max (p0.val + p1.val)
          (if p2.val ≥ p4.val + min p3.val p5.val
           then p0.val + p3.val + p4.val + p5.val
           else p0.val + p2.val + max p3.val p5.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 p2 p3 p4 p5 : Std.I64)
        (hlen : piles.val.length = 6)
        (hpiles : piles.val = [p0, p1, p2, p3, p4, p5])
        (hb0 : 1 ≤ p0.val ∧ p0.val ≤ 10000)
        (hb1 : 1 ≤ p1.val ∧ p1.val ≤ 10000)
        (hb2 : 1 ≤ p2.val ∧ p2.val ≤ 10000)
        (hb3 : 1 ≤ p3.val ∧ p3.val ≤ 10000)
        (hb4 : 1 ≤ p4.val ∧ p4.val ≤ 10000)
        (hb5 : 1 ≤ p5.val ∧ p5.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧
          r.val = max (p0.val + p1.val)
            (if p2.val ≥ p4.val + min p3.val p5.val
             then p0.val + p3.val + p4.val + p5.val
             else p0.val + p2.val + max p3.val p5.val)) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{len(piles)-1} piles[i] - piles[2].
    Preconditions: len(piles) >= 3; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_10 (piles : Slice Std.I64) (p0 p1 p2 : Std.I64) (rest : List Std.I64)
      (hlen_ge : 3 ≤ piles.val.length)
      (hpiles : piles.val = p0 :: p1 :: p2 :: rest)
      (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val ≤ (pvals piles).sum - p2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 p2 : Std.I64) (rest : List Std.I64)
        (hlen_ge : 3 ≤ piles.val.length)
        (hpiles : piles.val = p0 :: p1 :: p2 :: rest)
        (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val ≤ (pvals piles).sum - p2.val) := by
    sorry

  /-- The function returns a result r and r >= piles[0] + max(piles[1], piles[3]).
    Preconditions: len(piles) >= 4; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_11 (piles : Slice Std.I64) (p0 p1 p2 p3 : Std.I64) (rest : List Std.I64)
      (hlen_ge : 4 ≤ piles.val.length)
      (hpiles : piles.val = p0 :: p1 :: p2 :: p3 :: rest)
      (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧ r.val ≥ p0.val + max p1.val p3.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 p2 p3 : Std.I64) (rest : List Std.I64)
        (hlen_ge : 4 ≤ piles.val.length)
        (hpiles : piles.val = p0 :: p1 :: p2 :: p3 :: rest)
        (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧ r.val ≥ p0.val + max p1.val p3.val) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{len(piles)-1} piles[i] - piles[2] - min(piles[1], piles[3]).
    Preconditions: len(piles) >= 4; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_12 (piles : Slice Std.I64) (p0 p1 p2 p3 : Std.I64) (rest : List Std.I64)
      (hlen_ge : 4 ≤ piles.val.length)
      (hpiles : piles.val = p0 :: p1 :: p2 :: p3 :: rest)
      (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r, stone_game_ii piles = ok r ∧
        r.val ≤ (pvals piles).sum - p2.val - min p1.val p3.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (piles : Slice Std.I64) (p0 p1 p2 p3 : Std.I64) (rest : List Std.I64)
        (hlen_ge : 4 ≤ piles.val.length)
        (hpiles : piles.val = p0 :: p1 :: p2 :: p3 :: rest)
        (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r, stone_game_ii piles = ok r ∧
          r.val ≤ (pvals piles).sum - p2.val - min p1.val p3.val) := by
    sorry

  /-- r' = k * r.
    Preconditions: len(piles) >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. Let k be a positive integer such that 1 <= k * piles[i] <= 10000 for all i. Let r be the result of stone_game_ii(piles) and r' be the result of stone_game_ii(k * piles). -/
  theorem spec_13 (piles piles' : Slice Std.I64) (k : ℤ)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hk : 1 ≤ k)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000)
      (hscale : pvals piles' = (pvals piles).map (fun x => k * x))
      (hbounds' : ∀ p ∈ piles'.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r r', stone_game_ii piles = ok r ∧ stone_game_ii piles' = ok r' ∧ r'.val = k * r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (piles piles' : Slice Std.I64) (k : ℤ)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hk : 1 ≤ k)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000)
        (hscale : pvals piles' = (pvals piles).map (fun x => k * x))
        (hbounds' : ∀ p ∈ piles'.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r r', stone_game_ii piles = ok r ∧ stone_game_ii piles' = ok r' ∧ r'.val = k * r.val) := by
    sorry

  /-- There exists an integer X such that 1 <= X <= min(2, len(piles)) and if Alice takes the first X piles on her first turn, then by both players playing optimally thereafter, Alice's total score is exactly r. Moreover, for every X' with 1 <= X' <= min(2, len(piles)), the total Alice can obtain by taking the first X' piles is at most r.
    Preconditions: len(piles) >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= 10000. -/
  theorem spec_14 (piles : Slice Std.I64)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000) :
      ∃ r X, stone_game_ii piles = ok r ∧
        1 ≤ X ∧ X ≤ Nat.min 2 (pvals piles).length ∧
        suffixSum (pvals piles) 0 - V (pvals piles) X (Nat.max 1 X) = r.val ∧
        (∀ X', 1 ≤ X' → X' ≤ Nat.min 2 (pvals piles).length →
          suffixSum (pvals piles) 0 - V (pvals piles) X' (Nat.max 1 X') ≤ r.val) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (piles : Slice Std.I64)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hbounds : ∀ p ∈ piles.val, 1 ≤ p.val ∧ p.val ≤ 10000), ∃ r X, stone_game_ii piles = ok r ∧
          1 ≤ X ∧ X ≤ Nat.min 2 (pvals piles).length ∧
          suffixSum (pvals piles) 0 - V (pvals piles) X (Nat.max 1 X) = r.val ∧
          (∀ X', 1 ≤ X' → X' ≤ Nat.min 2 (pvals piles).length →
            suffixSum (pvals piles) 0 - V (pvals piles) X' (Nat.max 1 X') ≤ r.val)) := by
    sorry

  /-- Let r be the result of stone_game_ii(piles) and r' be the result of stone_game_ii(piles'). Then r' >= r.
    Preconditions: len(piles) = len(piles') >= 1; len(piles) <= 100; for every i with 0 <= i < len(piles), 1 <= piles[i] <= piles'[i] <= 10000. -/
  theorem spec_15 (piles piles' : Slice Std.I64)
      (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
      (hmono : List.Forall₂ (fun x y => 1 ≤ x ∧ x ≤ y ∧ y ≤ 10000) (pvals piles) (pvals piles')) :
      ∃ r r', stone_game_ii piles = ok r ∧ stone_game_ii piles' = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (piles piles' : Slice Std.I64)
        (hlen_pos : 1 ≤ piles.val.length) (hlen_le : piles.val.length ≤ 100)
        (hmono : List.Forall₂ (fun x y => 1 ≤ x ∧ x ≤ y ∧ y ≤ 10000) (pvals piles) (pvals piles')), ∃ r r', stone_game_ii piles = ok r ∧ stone_game_ii piles' = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  end AegisSpec.StoneGameIi
