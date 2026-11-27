import Aegis.StoneGameV.Code.Funs

/-!
# Specifications of `Aegis.StoneGameV.stone_game_v`

LeetCode problem `stone-game-v`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.StoneGameV

namespace AegisSpec.StoneGameV

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def sum (s : Slice Std.I64) (l r : ℕ) : ℤ := (((vals s).drop l).take (r - l)).sum

def candidate (s : Slice Std.I64) (l r k : ℕ) (bl br : ℤ) : ℤ :=
  let L := sum s l k
  let R := sum s k r
  if L < R then L + bl else if R < L then R + br else L + max bl br

def best (s : Slice Std.I64) (l r : ℕ) : ℤ :=
  if r - l ≤ 1 then 0
  else
    let v := (List.finRange (r - l - 1)).map fun (j : Fin (r - l - 1)) =>
      candidate s l r (l + 1 + (j : ℕ)) (best s l (l + 1 + (j : ℕ)))
        (best s (l + 1 + (j : ℕ)) r)
    v.max?.getD 0
termination_by r - l
decreasing_by
  all_goals omega

def value (s : Slice Std.I64) (l r k : ℕ) : ℤ :=
  candidate s l r k (best s l k) (best s k r)

def Step (s : Slice Std.I64) (a b k a' b' : ℕ) : Prop :=
  a < k ∧ k < b ∧
    ((sum s a k < sum s k b ∧ a' = a ∧ b' = k) ∨
     (sum s k b < sum s a k ∧ a' = k ∧ b' = b) ∨
     (sum s a k = sum s k b ∧ ((a' = a ∧ b' = k) ∨ (a' = k ∧ b' = b))))

def IsPlay (s : Slice Std.I64) (t : ℕ) (lo hi sp : ℕ → ℕ) : Prop :=
  lo 0 = 0 ∧ hi 0 = s.val.length ∧
    (∀ j, j < t → Step s (lo j) (hi j) (sp j) (lo (j + 1)) (hi (j + 1))) ∧
    hi t - lo t = 1

def playScore (s : Slice Std.I64) (t : ℕ) (lo hi sp : ℕ → ℕ) : ℤ :=
  (Finset.range t).sum (fun j => min (sum s (lo j) (sp j)) (sum s (sp j) (hi j)))

def HasPlayScore (s : Slice Std.I64) (v : ℤ) : Prop :=
  ∃ (t : ℕ) (lo hi sp : ℕ → ℕ), IsPlay s t lo hi sp ∧ playScore s t lo hi sp = v

def minVal (s : Slice Std.I64) : ℤ := ((vals s).min?).getD 0

def revVals (s : Slice Std.I64) : List Std.I64 := s.val.reverse

/-- Let sum(l,r) = Σ_{i=l}^{r-1} stoneValue[i] for 0 <= l < r <= n. Define best(l,r) for 0 <= l < r <= n as follows. If r - l = 1, then best(l,r) = 0. If r - l >= 2, then for each k with l < k < r let L = sum(l,k) and R = sum(k,r), and let value(l,r,k) be: L + best(l,k) when L < R; R + best(k,r) when R < L; and L + max(best(l,k), best(k,r)) when L = R. Then best(l,r) = max{value(l,r,k) | l < k < r}. The function returns a result r and r = best(0,n).
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_1 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000) :
    ∃ r : Std.I64, stone_game_v s = ok r ∧ r.val = best s 0 s.val.length := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000), ∃ r : Std.I64, stone_game_v s = ok r ∧ r.val = best s 0 s.val.length) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_2 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000) :
    ∃ r : Std.I64, stone_game_v s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000), ∃ r : Std.I64, stone_game_v s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_3 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), 0 ≤ r.val) := by
  sorry

/-- Let S = Σ_{i=0}^{n-1} stoneValue[i] and let m = min{stoneValue[i] | 0 <= i < n}. Whenever the function returns a result r, r <= S - m.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_4 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    r.val ≤ sum s 0 s.val.length - minVal s := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), r.val ≤ sum s 0 s.val.length - minVal s) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(stoneValue). The input satisfies n = 1 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_5 (s : Slice Std.I64)
    (hn : s.val.length = 1)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn : s.val.length = 1)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = min(stoneValue[0], stoneValue[1]).
  Preconditions: Let n = len(stoneValue). The input satisfies n = 2 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_6 (s : Slice Std.I64)
    (hn : s.val.length = 2)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    r.val = min (s.val.get ⟨0, by omega⟩).val (s.val.get ⟨1, by omega⟩).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn : s.val.length = 2)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), r.val = min (s.val.get ⟨0, by omega⟩).val (s.val.get ⟨1, by omega⟩).val) := by
  sorry

/-- Let sum(l,r) = Σ_{i=l}^{r-1} stoneValue[i]. A legal play is a finite sequence of intervals [l_0,r_0),...,[l_t,r_t) such that [l_0,r_0)=[0,n), r_t-l_t=1, and for each j<t there is k_j with l_j<k_j<r_j for which: if sum(l_j,k_j) < sum(k_j,r_j) then [l_{j+1},r_{j+1})=[l_j,k_j); if sum(l_j,k_j) > sum(k_j,r_j) then [l_{j+1},r_{j+1})=[k_j,r_j); if the two sums are equal then [l_{j+1},r_{j+1}) is either [l_j,k_j) or [k_j,r_j). Its accumulated score is Σ_{j=0}^{t-1} min(sum(l_j,k_j), sum(k_j,r_j)). Whenever the function returns a result r, there exists a legal play whose accumulated score is exactly r.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_7 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    HasPlayScore s r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), HasPlayScore s r.val) := by
  sorry

/-- Whenever the function returns a result r, for every sequence of choices that follows the game rules starting from the whole row [0,n) and ending when one stone remains, the sum of the smaller-side sums obtained at the rounds, with either side allowed when the two sums are equal, is at most r.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_8 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    ∀ (t : ℕ) (lo hi sp : ℕ → ℕ), IsPlay s t lo hi sp → playScore s t lo hi sp ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), ∀ (t : ℕ) (lo hi sp : ℕ → ℕ), IsPlay s t lo hi sp → playScore s t lo hi sp ≤ r.val) := by
  sorry

/-- Let sum(l,r) = Σ_{i=l}^{r-1} stoneValue[i]. Whenever the function returns a result r, for every integer k with 1 <= k < n, r >= min(sum(0,k), sum(k,n)).
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_9 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    ∀ k : ℕ, 1 ≤ k → k < s.val.length → min (sum s 0 k) (sum s k s.val.length) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), ∀ k : ℕ, 1 ≤ k → k < s.val.length → min (sum s 0 k) (sum s k s.val.length) ≤ r.val) := by
  sorry

/-- Let rev be the list of length n with rev[i] = stoneValue[n-1-i] for every i with 0 <= i < n. If the function returns r on stoneValue and returns r_rev on rev, then r = r_rev.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_10 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (srev : Slice Std.I64) (hrev : srev.val = revVals s)
    (r rrev : Std.I64) (hr : stone_game_v s = ok r) (hrrev : stone_game_v srev = ok rrev) :
    r.val = rrev.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (srev : Slice Std.I64) (hrev : srev.val = revVals s)
    (r rrev : Std.I64) (hr : stone_game_v s = ok r) (hrrev : stone_game_v srev = ok rrev), r.val = rrev.val) := by
  sorry

/-- If the function returns r on stoneValue and returns r_c on the list whose i-th entry is c*stoneValue[i], then r_c = c*r.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. Let c be a positive integer such that 1 <= c*stoneValue[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_11 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (c : ℤ) (hc : 1 ≤ c)
    (hcbounds : ∀ (i : ℕ) (hi : i < s.val.length),
      1 ≤ c * (s.val.get ⟨i, hi⟩).val ∧ c * (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (scaled : Slice Std.I64) (hscaled : vals scaled = (vals s).map (fun x => c * x))
    (r rc : Std.I64) (hr : stone_game_v s = ok r) (hrc : stone_game_v scaled = ok rc) :
    rc.val = c * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (c : ℤ) (hc : 1 ≤ c)
    (hcbounds : ∀ (i : ℕ) (hi : i < s.val.length),
      1 ≤ c * (s.val.get ⟨i, hi⟩).val ∧ c * (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (scaled : Slice Std.I64) (hscaled : vals scaled = (vals s).map (fun x => c * x))
    (r rc : Std.I64) (hr : stone_game_v s = ok r) (hrc : stone_game_v scaled = ok rc), rc.val = c * r.val) := by
  sorry

/-- Let S = Σ_{i=0}^{n-1} stoneValue[i]. Whenever the function returns a result r, for every legal play whose accumulated score equals r, if f is the value of the single stone remaining at the end of that play, then r + f <= S.
  Preconditions: Let n = len(stoneValue). The input satisfies 1 <= n <= 500 and, for every i with 0 <= i < n, 1 <= stoneValue[i] <= 1000000. -/
theorem spec_12 (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r) :
    ∀ (t : ℕ) (lo hi sp : ℕ → ℕ), IsPlay s t lo hi sp → playScore s t lo hi sp = r.val →
      r.val + sum s (lo t) (hi t) ≤ sum s 0 s.val.length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 500)
    (hlo : ∀ (i : ℕ) (hi : i < s.val.length), 1 ≤ (s.val.get ⟨i, hi⟩).val)
    (hhi : ∀ (i : ℕ) (hi : i < s.val.length), (s.val.get ⟨i, hi⟩).val ≤ 1000000)
    (r : Std.I64) (hr : stone_game_v s = ok r), ∀ (t : ℕ) (lo hi sp : ℕ → ℕ), IsPlay s t lo hi sp → playScore s t lo hi sp = r.val →
      r.val + sum s (lo t) (hi t) ≤ sum s 0 s.val.length) := by
  sorry

end AegisSpec.StoneGameV
