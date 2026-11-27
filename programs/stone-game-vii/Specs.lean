import Aegis.StoneGameVii.Code.Funs

/-!
# Specifications of `Aegis.StoneGameVii.stone_game_vii`

LeetCode problem `stone-game-vii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.StoneGameVii

  def vals (l : List Std.I64) : List ℤ := l.map fun x => x.val

  def sliceSum (l : List Std.I64) : ℤ := (vals l).sum

  def sliceMax (l : List Std.I64) : ℤ := (vals l).foldr max 0

  def descVals (l : List Std.I64) : List ℤ := (vals l).mergeSort (fun a b => b ≤ a)

  def sumLargest (l : List Std.I64) (m : ℕ) : ℤ := (descVals l).take m |>.sum

  def segSum (l : List ℤ) (a b : ℕ) : ℤ := ((l.drop a).take (b + 1 - a)).sum

  def V (l : List ℤ) (a b : ℕ) : ℤ :=
    if _h : a < b then
      max (segSum l (a + 1) b - V l (a + 1) b) (segSum l a (b - 1) - V l a (b - 1))
    else 0
  termination_by b - a
  decreasing_by all_goals omega

  /-- The function returns a result r, and r = V(0, len(stones)-1), where V(l,r) is defined for 0 <= l <= r < len(stones) by V(l,l) = 0, and for l < r by V(l,r) = max( sum(l+1,r) - V(l+1,r), sum(l,r-1) - V(l,r-1) ), with sum(a,b) = stones[a] + ... + stones[b] for a <= b, and sum(a,b) = 0 when a > b.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_1 (stones : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000) :
      ∃ r, Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
        r.val = V (vals stones.val) 0 (stones.val.length - 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000), ∃ r, Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
          r.val = V (vals stones.val) 0 (stones.val.length - 1)) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, or panic) for every input satisfying the preconditions.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_2 (stones : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000) :
      ∃ r, Aegis.StoneGameVii.stone_game_vii stones = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000), ∃ r, Aegis.StoneGameVii.stone_game_vii stones = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_3 (stones : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000), ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{len(stones)-1} stones[i].
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_4 (stones : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r → r.val ≤ sliceSum stones.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000), ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r → r.val ≤ sliceSum stones.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= max_{0 <= i < len(stones)} stones[i] * (len(stones) / 2), where / is integer division.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_5 (stones : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r →
        r.val ≤ sliceMax stones.val * ((stones.val.length / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000), ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r →
          r.val ≤ sliceMax stones.val * ((stones.val.length / 2 : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r, and r = (len(stones) / 2) * c, where / is integer division.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; there exists an integer c with 1 <= c <= 1000 such that for every i with 0 <= i < len(stones), stones[i] = c. -/
  theorem spec_6 (stones : Slice Std.I64) (c : ℤ)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hc_lo : 1 ≤ c) (hc_hi : c ≤ 1000)
      (hconst : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val = c) :
      ∃ r, Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
        r.val = ((stones.val.length / 2 : ℕ) : ℤ) * c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (stones : Slice Std.I64) (c : ℤ)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hc_lo : 1 ≤ c) (hc_hi : c ≤ 1000)
        (hconst : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val = c), ∃ r, Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
          r.val = ((stones.val.length / 2 : ℕ) : ℤ) * c) := by
    sorry

  /-- Let rev be the array of length len(stones) with rev[i] = stones[len(stones)-1-i] for 0 <= i < len(stones). If r is the result of stone_game_vii(stones) and r' is the result of stone_game_vii(rev), then r' = r. Both calls return results.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_7 (stones rev : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000)
      (hrev : rev.val = stones.val.reverse) :
      ∃ r r', Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
        Aegis.StoneGameVii.stone_game_vii rev = ok r' ∧ r' = r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (stones rev : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000)
        (hrev : rev.val = stones.val.reverse), ∃ r r', Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
          Aegis.StoneGameVii.stone_game_vii rev = ok r' ∧ r' = r) := by
    sorry

  /-- If r is the result of stone_game_vii(stones) and r' is the result of stone_game_vii(shifted), then r' = r + c * (len(stones) / 2), where / is integer division. Both calls return results.
    Preconditions: stones satisfies len(stones) >= 2, len(stones) <= 1000, and 1 <= stones[i] <= 1000 for all i. Let c be an integer such that for every i, 1 <= stones[i] + c <= 1000. Define shifted[i] = stones[i] + c. -/
  theorem spec_8 (stones shifted : Slice Std.I64) (c : ℤ)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000)
      (hc : ∀ (i : ℕ) (hi : i < stones.val.length),
        1 ≤ (stones.val[i]'hi).val + c ∧ (stones.val[i]'hi).val + c ≤ 1000)
      (hshifted : shifted.val.map (fun x => x.val) = stones.val.map (fun x => x.val + c)) :
      ∃ r r', Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
        Aegis.StoneGameVii.stone_game_vii shifted = ok r' ∧
        r'.val = r.val + c * ((stones.val.length / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (stones shifted : Slice Std.I64) (c : ℤ)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000)
        (hc : ∀ (i : ℕ) (hi : i < stones.val.length),
          1 ≤ (stones.val[i]'hi).val + c ∧ (stones.val[i]'hi).val + c ≤ 1000)
        (hshifted : shifted.val.map (fun x => x.val) = stones.val.map (fun x => x.val + c)), ∃ r r', Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
          Aegis.StoneGameVii.stone_game_vii shifted = ok r' ∧
          r'.val = r.val + c * ((stones.val.length / 2 : ℕ) : ℤ)) := by
    sorry

  /-- If r is the result of stone_game_vii(stones) and r' is the result of stone_game_vii(scaled), then r' = k * r. Both calls return results.
    Preconditions: stones satisfies len(stones) >= 2, len(stones) <= 1000, and 1 <= stones[i] <= 1000 for all i. Let k be a positive integer such that for every i, 1 <= k * stones[i] <= 1000. Define scaled[i] = k * stones[i]. -/
  theorem spec_9 (stones scaled : Slice Std.I64) (k : ℤ)
      (hk_pos : 0 < k)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000)
      (hk : ∀ (i : ℕ) (hi : i < stones.val.length),
        1 ≤ k * (stones.val[i]'hi).val ∧ k * (stones.val[i]'hi).val ≤ 1000)
      (hscaled : scaled.val.map (fun x => x.val) = stones.val.map (fun x => k * x.val)) :
      ∃ r r', Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
        Aegis.StoneGameVii.stone_game_vii scaled = ok r' ∧ r'.val = k * r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (stones scaled : Slice Std.I64) (k : ℤ)
        (hk_pos : 0 < k)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000)
        (hk : ∀ (i : ℕ) (hi : i < stones.val.length),
          1 ≤ k * (stones.val[i]'hi).val ∧ k * (stones.val[i]'hi).val ≤ 1000)
        (hscaled : scaled.val.map (fun x => x.val) = stones.val.map (fun x => k * x.val)), ∃ r r', Aegis.StoneGameVii.stone_game_vii stones = ok r ∧
          Aegis.StoneGameVii.stone_game_vii scaled = ok r' ∧ r'.val = k * r.val) := by
    sorry

  /-- If r1 is the result of stone_game_vii(stones1) and r2 is the result of stone_game_vii(stones2), then r1 <= r2. Both calls return results.
    Preconditions: stones1 and stones2 have equal length n with 2 <= n <= 1000, and for every i, 1 <= stones1[i] <= stones2[i] <= 1000. -/
  theorem spec_10 (stones1 stones2 : Slice Std.I64) (n : ℕ)
      (hlen1 : stones1.val.length = n) (hlen2 : stones2.val.length = n)
      (hn_lo : 2 ≤ n) (hn_hi : n ≤ 1000)
      (hentry : ∀ (i : ℕ) (h1 : i < stones1.val.length) (h2 : i < stones2.val.length),
        1 ≤ (stones1.val[i]'h1).val ∧
        (stones1.val[i]'h1).val ≤ (stones2.val[i]'h2).val ∧
        (stones2.val[i]'h2).val ≤ 1000) :
      ∃ r1 r2, Aegis.StoneGameVii.stone_game_vii stones1 = ok r1 ∧
        Aegis.StoneGameVii.stone_game_vii stones2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (stones1 stones2 : Slice Std.I64) (n : ℕ)
        (hlen1 : stones1.val.length = n) (hlen2 : stones2.val.length = n)
        (hn_lo : 2 ≤ n) (hn_hi : n ≤ 1000)
        (hentry : ∀ (i : ℕ) (h1 : i < stones1.val.length) (h2 : i < stones2.val.length),
          1 ≤ (stones1.val[i]'h1).val ∧
          (stones1.val[i]'h1).val ≤ (stones2.val[i]'h2).val ∧
          (stones2.val[i]'h2).val ≤ 1000), ∃ r1 r2, Aegis.StoneGameVii.stone_game_vii stones1 = ok r1 ∧
          Aegis.StoneGameVii.stone_game_vii stones2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= the sum of the largest floor(len(stones)/2) values in stones, where / denotes integer division.
    Preconditions: len(stones) >= 2 and len(stones) <= 1000; for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
  theorem spec_11 (stones : Slice Std.I64)
      (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
      (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
      (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r →
        r.val ≤ sumLargest stones.val (stones.val.length / 2) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (stones : Slice Std.I64)
        (hlen_lo : 2 ≤ stones.val.length) (hlen_hi : stones.val.length ≤ 1000)
        (hpos : ∀ (i : ℕ) (hi : i < stones.val.length), 1 ≤ (stones.val[i]'hi).val)
        (hsmall : ∀ (i : ℕ) (hi : i < stones.val.length), (stones.val[i]'hi).val ≤ 1000), ∀ r, Aegis.StoneGameVii.stone_game_vii stones = ok r →
          r.val ≤ sumLargest stones.val (stones.val.length / 2)) := by
    sorry

  end AegisSpec.StoneGameVii
