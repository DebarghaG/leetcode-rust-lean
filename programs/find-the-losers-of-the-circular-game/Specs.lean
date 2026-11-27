import Aegis.CircularGameLosers.Code.Funs

/-!
# Specifications of `Aegis.CircularGameLosers.circular_game_losers`

LeetCode problem `find-the-losers-of-the-circular-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CircularGameLosers

def pos (k n : ℤ) (t : ℕ) : ℤ :=
  (k * (t : ℤ) * ((t : ℤ) + 1)) / 2 |>.emod n

def IsFirstRepeat (P : ℕ → ℤ) (T : ℕ) : Prop :=
  1 ≤ T ∧ (∃ s, s < T ∧ P s = P T) ∧ ∀ t, 1 ≤ t → t < T → ¬∃ s, s < t ∧ P s = P t

def losersList (n k : ℤ) (T : ℕ) : List ℤ :=
  ((List.range n.toNat).filter
      (fun i => (List.range T).all (fun t => decide (pos k n t ≠ (i : ℤ))))).map
    (fun i => (i : ℤ) + 1)

def seqFromTwo (n : ℤ) : List ℤ :=
  (List.range (n.toNat - 1)).map (fun i => (i : ℤ) + 2)

def contents (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

/-- Let pos(t) be the least nonnegative residue of k * t * (t+1) / 2 modulo n for each integer t >= 0 (the division is exact because t*(t+1) is even). Let T be the least integer t >= 1 such that pos(t) = pos(s) for some integer s with 0 <= s < t; such T exists and satisfies 1 <= T <= n. Whenever the function returns a result r, r is exactly the list of all integers f with 1 <= f <= n and f-1 not in {pos(t) | 0 <= t < T}, listed in strictly increasing order.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_1 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r) :
    contents r = losersList n.val k.val T := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r), contents r = losersList n.val k.val T) := by
  sorry

/-- The function returns a result r (a Vec of 64-bit signed integers); it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_2 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.CircularGameLosers.circular_game_losers n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50), ∃ r : alloc.vec.Vec Std.I64, Aegis.CircularGameLosers.circular_game_losers n k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is strictly increasing: for every i and j with 0 <= i < j < len(r), r[i] < r[j].
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_3 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length) (hij : i < j) :
    (r.val.get ⟨i, hi⟩).val < (r.val.get ⟨j, hj⟩).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length) (hij : i < j), (r.val.get ⟨i, hi⟩).val < (r.val.get ⟨j, hj⟩).val) := by
  sorry

/-- Whenever the function returns a result r, every element of r is a valid friend number: for every i with 0 <= i < len(r), 1 <= r[i] <= n.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_4 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length) :
    1 ≤ (r.val.get ⟨i, hi⟩).val ∧ (r.val.get ⟨i, hi⟩).val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length), 1 ≤ (r.val.get ⟨i, hi⟩).val ∧ (r.val.get ⟨i, hi⟩).val ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, friend 1 is not a loser: for every i with 0 <= i < len(r), r[i] != 1.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_5 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length) :
    (r.val.get ⟨i, hi⟩).val ≠ 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val ≠ 1) := by
  sorry

/-- Let pos(t) = (k * t * (t+1) / 2) mod n (least nonnegative residue) and let T be the least t >= 1 such that pos(t) = pos(s) for some s with 0 <= s < t. Whenever the function returns a result r, every element of r is a non-receiver: for every i with 0 <= i < len(r) and every t with 0 <= t < T, pos(t) != r[i] - 1.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_6 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length) (t : ℕ) (ht : t < T) :
    pos k.val n.val t ≠ (r.val.get ⟨i, hi⟩).val - 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length) (t : ℕ) (ht : t < T), pos k.val n.val t ≠ (r.val.get ⟨i, hi⟩).val - 1) := by
  sorry

/-- Let pos(t) = (k * t * (t+1) / 2) mod n (least nonnegative residue) and let T be the least t >= 1 such that pos(t) = pos(s) for some s with 0 <= s < t. Whenever the function returns a result r, every non-receiver appears in r: for every integer f with 1 <= f <= n, if for all t with 0 <= t < T we have pos(t) != f - 1, then there exists i with 0 <= i < len(r) and r[i] = f.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_7 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (f : ℤ) (hf1 : 1 ≤ f) (hfn : f ≤ n.val)
    (hf : ∀ t, t < T → pos k.val n.val t ≠ f - 1) :
    ∃ i : ℕ, ∃ hi : i < r.val.length, (r.val.get ⟨i, hi⟩).val = f := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (f : ℤ) (hf1 : 1 ≤ f) (hfn : f ≤ n.val)
    (hf : ∀ t, t < T → pos k.val n.val t ≠ f - 1), ∃ i : ℕ, ∃ hi : i < r.val.length, (r.val.get ⟨i, hi⟩).val = f) := by
  sorry

/-- Let T be the least t >= 1 such that (k * t * (t+1) / 2) mod n = (k * s * (s+1) / 2) mod n for some s with 0 <= s < t. Whenever the function returns a result r, len(r) = n - T.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_8 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r) :
    (r.val.length : ℤ) = n.val - (T : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (T : ℕ) (hT : IsFirstRepeat (pos k.val n.val) T)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r), (r.val.length : ℤ) = n.val - (T : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, the length of r is between 0 and n-1 inclusive: 0 <= len(r) <= n - 1.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_9 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r) :
    0 ≤ (r.val.length : ℤ) ∧ (r.val.length : ℤ) ≤ n.val - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r), 0 ≤ (r.val.length : ℤ) ∧ (r.val.length : ℤ) ≤ n.val - 1) := by
  sorry

/-- Whenever the function returns a result r, r is the list [2, 3, ..., n] (which is empty when n = 1) if and only if k = n.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_10 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r) :
    contents r = seqFromTwo n.val ↔ k.val = n.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r), contents r = seqFromTwo n.val ↔ k.val = n.val) := by
  sorry

/-- Whenever the function returns a result r, each element is at least its index plus 2: for every i with 0 <= i < len(r), r[i] >= i + 2.
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_11 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length) :
    (i : ℤ) + 2 ≤ (r.val.get ⟨i, hi⟩).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length), (i : ℤ) + 2 ≤ (r.val.get ⟨i, hi⟩).val) := by
  sorry

/-- Whenever the function returns a result r, each element is bounded above by n minus the number of later elements: for every i with 0 <= i < len(r), r[i] <= n - (len(r) - 1 - i).
  Preconditions: n and k are 64-bit signed integers with 1 <= k <= n <= 50. -/
theorem spec_12 (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length) :
    (r.val.get ⟨i, hi⟩).val ≤ n.val - ((r.val.length : ℤ) - 1 - (i : ℤ)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val)
    (hn50 : n.val ≤ 50)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CircularGameLosers.circular_game_losers n k = ok r)
    (i : ℕ) (hi : i < r.val.length), (r.val.get ⟨i, hi⟩).val ≤ n.val - ((r.val.length : ℤ) - 1 - (i : ℤ))) := by
  sorry

end AegisSpec.CircularGameLosers
