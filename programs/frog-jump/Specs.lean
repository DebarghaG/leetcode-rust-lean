import Aegis.CanCross.Code.Funs

/-!
# Specifications of `Aegis.CanCross.can_cross`

LeetCode problem `frog-jump`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanCross

  set_option autoImplicit false

  def slen (stones : Aeneas.Std.Slice Aeneas.Std.I64) : ℕ := stones.val.length

  def stoneAt (stones : Aeneas.Std.Slice Aeneas.Std.I64) (i : ℕ) : ℤ :=
    (stones.val.getD i default).val

  def jump (stones : Aeneas.Std.Slice Aeneas.Std.I64) (idx : ℕ → ℕ) (t : ℕ) : ℤ :=
    stoneAt stones (idx t) - stoneAt stones (idx (t - 1))

  def IsCrossing (stones : Aeneas.Std.Slice Aeneas.Std.I64) (m : ℕ) (idx : ℕ → ℕ) : Prop :=
    1 ≤ m ∧
      idx 0 = 0 ∧
      idx m = slen stones - 1 ∧
      (∀ t, t ≤ m → idx t < slen stones) ∧
      (∀ t, t < m → idx t < idx (t + 1)) ∧
      jump stones idx 1 = 1 ∧
      (∀ t, 2 ≤ t → t ≤ m →
        jump stones idx t > 0 ∧
          (jump stones idx t = jump stones idx (t - 1) - 1 ∨
            jump stones idx t = jump stones idx (t - 1) ∨
            jump stones idx t = jump stones idx (t - 1) + 1))

  def ValidCrossing (stones : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    ∃ (m : ℕ) (idx : ℕ → ℕ), IsCrossing stones m idx

  def ValidCrossingWithBoundedLastJump (stones : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    ∃ (m : ℕ) (idx : ℕ → ℕ),
      IsCrossing stones m idx ∧ 1 ≤ jump stones idx m ∧ jump stones idx m ≤ (slen stones : ℤ) - 1

  theorem slen_eq_len (stones : Aeneas.Std.Slice Aeneas.Std.I64) :
      (Aeneas.Std.Slice.len stones).val = slen stones := by
    simp [slen, Aeneas.Std.Slice.len, Aeneas.Std.Slice.val, Aeneas.Std.Usize.ofNatCore]

  theorem stoneAt_eq (stones : Aeneas.Std.Slice Aeneas.Std.I64) (i : ℕ) (h : i < slen stones) :
      stoneAt stones i = (stones.val[i]).val := by
    simp only [stoneAt, List.getD_eq_getElem (n := i) (hn := h)]

  /-- Let n = len(stones). The function returns a result r (it does not fail). Call a finite sequence of indices i_0, i_1, ..., i_m a valid crossing when: m >= 1; i_0 = 0; i_m = n - 1; 0 <= i_0 < i_1 < ... < i_m < n; and, writing d_t = stones[i_t] - stones[i_{t-1}] for t = 1, ..., m, we have d_1 = 1 and for every t with 2 <= t <= m, d_t > 0 and d_t is either d_{t-1} - 1, d_{t-1}, or d_{t-1} + 1. Then r = true if and only if there exists a valid crossing; equivalently, r = false if and only if no valid crossing exists.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]. -/
  theorem spec_1 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1)) :
      ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ (r = true ↔ ValidCrossing stones) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1)), ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ (r = true ↔ ValidCrossing stones)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (either true or false); it does not panic, overflow, or access an out-of-bounds index.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]. -/
  theorem spec_2 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1)) :
      ∃ r, Aegis.CanCross.can_cross stones = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1)), ∃ r, Aegis.CanCross.can_cross stones = Result.ok r) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]; stones[1] != 1. -/
  theorem spec_3 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
      (hsecond : stoneAt stones 1 ≠ 1) :
      ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
        (hsecond : stoneAt stones 1 ≠ 1), ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = false) := by
    sorry

  /-- Let n = len(stones). If stones[n - 1] > n*(n - 1)/2, then the function returns a result r and r = false.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]. -/
  theorem spec_4 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
      (hlast_big : stoneAt stones (slen stones - 1) > ↑((slen stones * (slen stones - 1)) / 2)) :
      ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
        (hlast_big : stoneAt stones (slen stones - 1) > ↑((slen stones * (slen stones - 1)) / 2)), ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = false) := by
    sorry

  /-- Let n = len(stones). If there is no index i with 0 <= i < n such that stones[i] = 2 or stones[i] = 3, then the function returns a result r and r = false.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]; n >= 3. -/
  theorem spec_5 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
      (hn_3 : 3 ≤ slen stones)
      (hno_2_3 : ∀ i, i < slen stones → stoneAt stones i ≠ 2 ∧ stoneAt stones i ≠ 3) :
      ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
        (hn_3 : 3 ≤ slen stones)
        (hno_2_3 : ∀ i, i < slen stones → stoneAt stones i ≠ 2 ∧ stoneAt stones i ≠ 3), ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = false) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]; stones[1] = 1; for every i with 1 <= i < n - 1, 1 <= stones[i + 1] - stones[i] <= 2. -/
  theorem spec_6 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
      (hsecond : stoneAt stones 1 = 1)
      (hgap : ∀ i, 1 ≤ i → i < slen stones - 1 →
        1 ≤ stoneAt stones (i + 1) - stoneAt stones i ∧
          stoneAt stones (i + 1) - stoneAt stones i ≤ 2) :
      ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
        (hsecond : stoneAt stones 1 = 1)
        (hgap : ∀ i, 1 ≤ i → i < slen stones - 1 →
          1 ≤ stoneAt stones (i + 1) - stoneAt stones i ∧
            stoneAt stones (i + 1) - stoneAt stones i ≤ 2), ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = true) := by
    sorry

  /-- Whenever the function returns a result r with r = true on input stones, it returns a result r' with r' = true on input stones'.
    Preconditions: Let n = len(stones). 2 <= n <= 1999; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]; stones' is a strictly increasing list of length n + 1 whose entries are exactly the entries of stones together with one additional integer p satisfying 0 < p < stones[n - 1] and p != stones[i] for all i with 0 <= i < n. -/
  theorem spec_7 (stones stones' : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 1999)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
      (hlen' : slen stones' = slen stones + 1)
      (hsorted' : ∀ i, i < slen stones' - 1 → stoneAt stones' i < stoneAt stones' (i + 1))
      (hentries' : ∃ p : ℤ,
        0 < p ∧ p < stoneAt stones (slen stones - 1) ∧
          (∀ i, i < slen stones → stoneAt stones i ≠ p) ∧
          (∀ i, i < slen stones' →
            stoneAt stones' i = p ∨ ∃ j, j < slen stones ∧ stoneAt stones j = stoneAt stones' i) ∧
          (∀ j, j < slen stones → ∃ i, i < slen stones' ∧ stoneAt stones' i = stoneAt stones j))
      (hstones_true : ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = true) :
      ∃ r', Aegis.CanCross.can_cross stones' = Result.ok r' ∧ r' = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (stones stones' : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 1999)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
        (hlen' : slen stones' = slen stones + 1)
        (hsorted' : ∀ i, i < slen stones' - 1 → stoneAt stones' i < stoneAt stones' (i + 1))
        (hentries' : ∃ p : ℤ,
          0 < p ∧ p < stoneAt stones (slen stones - 1) ∧
            (∀ i, i < slen stones → stoneAt stones i ≠ p) ∧
            (∀ i, i < slen stones' →
              stoneAt stones' i = p ∨ ∃ j, j < slen stones ∧ stoneAt stones j = stoneAt stones' i) ∧
            (∀ j, j < slen stones → ∃ i, i < slen stones' ∧ stoneAt stones' i = stoneAt stones j))
        (hstones_true : ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = true), ∃ r', Aegis.CanCross.can_cross stones' = Result.ok r' ∧ r' = true) := by
    sorry

  /-- Let n = len(stones). If the function returns a result r with r = true, then there exists a finite sequence i_0, i_1, ..., i_m such that m >= 1, i_0 = 0, i_m = n - 1, 0 <= i_0 < i_1 < ... < i_m < n, the jump lengths d_t = stones[i_t] - stones[i_{t-1}] for t = 1, ..., m satisfy d_1 = 1 and for every t with 2 <= t <= m, d_t > 0 and d_t is either d_{t-1} - 1, d_{t-1}, or d_{t-1} + 1, and moreover 1 <= d_m <= n - 1.
    Preconditions: Let n = len(stones). 2 <= n <= 2000; stones[0] = 0; for every i with 0 <= i < n, 0 <= stones[i] <= 2^31 - 1; for every i with 0 <= i < n - 1, stones[i] < stones[i + 1]. -/
  theorem spec_8 (stones : Aeneas.Std.Slice Aeneas.Std.I64)
      (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
      (hfirst : stoneAt stones 0 = 0)
      (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
      (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
      (hret : ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = true) :
      ValidCrossingWithBoundedLastJump stones := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (stones : Aeneas.Std.Slice Aeneas.Std.I64)
        (hn_ge : 2 ≤ slen stones) (hn_le : slen stones ≤ 2000)
        (hfirst : stoneAt stones 0 = 0)
        (hrange : ∀ i, i < slen stones → 0 ≤ stoneAt stones i ∧ stoneAt stones i ≤ 2 ^ 31 - 1)
        (hsorted : ∀ i, i < slen stones - 1 → stoneAt stones i < stoneAt stones (i + 1))
        (hret : ∃ r, Aegis.CanCross.can_cross stones = Result.ok r ∧ r = true), ValidCrossingWithBoundedLastJump stones) := by
    sorry

  end AegisSpec.CanCross
