import Aegis.MinimumAddedCoins.Code.Funs

/-!
# Specifications of `Aegis.MinimumAddedCoins.minimum_added_coins`

LeetCode problem `minimum-number-of-coins-to-be-added`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumAddedCoins

open Aegis.MinimumAddedCoins (minimum_added_coins)

def coinVals (coins : Slice Std.I64) : List ℤ := coins.val.map (fun c => c.val)

def IsSubsetSum (l : List ℤ) (x : ℤ) : Prop :=
  ∃ B : List ℤ, B.Sublist l ∧ B.sum = x

def CoversUpTo (coins added : List ℤ) (T : ℤ) : Prop :=
  ∀ x : ℤ, 1 ≤ x → x ≤ T → IsSubsetSum (coins ++ added) x

def CanAddCoins (coins : List ℤ) (T k : ℤ) : Prop :=
  ∃ A : List ℤ, (A.length : ℤ) = k ∧ (∀ a ∈ A, 1 ≤ a) ∧ CoversUpTo coins A T

def IsLeastCanAdd (coins : List ℤ) (T k : ℤ) : Prop :=
  0 ≤ k ∧ CanAddCoins coins T k ∧ ∀ k' : ℤ, 0 ≤ k' → CanAddCoins coins T k' → k ≤ k'

def sumLE (l : List ℤ) (v : ℤ) : ℤ := (l.filter (fun a => a ≤ v)).sum

def doubleIter : ℕ → ℤ → ℤ
  | 0, R => R
  | n + 1, R => doubleIter n (2 * R + 1)

noncomputable def leastPowStep (a v : ℤ) : ℕ :=
  by classical exact if h : ∃ n : ℕ, v ≤ a * 2 ^ n then Nat.find h else 0

noncomputable def greedyAbsorb (st : ℤ × ℤ) (v : ℤ) : ℤ × ℤ :=
  let n := leastPowStep (st.1 + 1) v
  (doubleIter n st.1 + v, st.2 + (n : ℤ))

noncomputable def greedyRun (sortedCoins : List ℤ) : ℤ × ℤ :=
  sortedCoins.foldl greedyAbsorb (0, 0)

noncomputable def greedyValue (sortedCoins : List ℤ) (T : ℤ) : ℤ :=
  let st := greedyRun sortedCoins
  st.2 + (leastPowStep (st.1 + 1) (T + 1) : ℤ)

/-- The function returns a result r. Let T = target. Then r is the least integer k >= 0 for which there exists a finite list A of length k, whose entries are positive integers (repetitions allowed), such that for every integer x with 1 <= x <= T there exist index sets I subset of {0,...,len(coins)-1} and J subset of {0,...,k-1} with sum_{i in I} coins[i] + sum_{j in J} A[j] = x. Each index is used at most once; equivalently, x is a sum of a sub-multiset of the original coins together with the added coins.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_1 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      IsLeastCanAdd (coinVals coins) target.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      IsLeastCanAdd (coinVals coins) target.val r.val) := by
  sorry

/-- For every coins and target satisfying the preconditions, the function returns a result r; in particular it does not fail through overflow, out-of-bounds access, or panic.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_2 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r) := by
  sorry

/-- Let T = target and let m be the least integer m >= 0 such that 2^m - 1 >= T. The function returns a result r satisfying 0 <= r <= m. Since T <= 100000, this also implies r <= 17.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_3 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧ 0 ≤ r.val ∧
      (∃ m : ℕ, target.val ≤ (2 : ℤ) ^ m - 1 ∧
        (∀ m' : ℕ, target.val ≤ (2 : ℤ) ^ m' - 1 → m ≤ m') ∧ r.val ≤ (m : ℤ)) ∧
      r.val ≤ 17 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧ 0 ≤ r.val ∧
      (∃ m : ℕ, target.val ≤ (2 : ℤ) ^ m - 1 ∧
        (∀ m' : ℕ, target.val ≤ (2 : ℤ) ^ m' - 1 → m ≤ m') ∧ r.val ≤ (m : ℤ)) ∧
      r.val ≤ 17) := by
  sorry

/-- Let T = target. The returned value r equals 0 if and only if for every integer v with 1 <= v <= T, the sum of all entries coins[i] with coins[i] <= v is at least v.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_4 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      (r.val = 0 ↔ ∀ v : ℤ, 1 ≤ v → v ≤ target.val → v ≤ sumLE (coinVals coins) v) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      (r.val = 0 ↔ ∀ v : ℤ, 1 ≤ v → v ≤ target.val → v ≤ sumLE (coinVals coins) v)) := by
  sorry

/-- If the function returns r, then r >= 1.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 2 <= coins[i] <= target. -/
theorem spec_5 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 2 ≤ c.val ∧ c.val ≤ target.val) :
    ∀ r : Std.I64, minimum_added_coins coins target = ok r → 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 2 ≤ c.val ∧ c.val ≤ target.val), ∀ r : Std.I64, minimum_added_coins coins target = ok r → 1 ≤ r.val) := by
  sorry

/-- Let n = len(coins), and let k be the least integer k >= 0 such that (n+1) * 2^k - 1 >= target. The function returns r = k.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, coins[i] = 1. -/
theorem spec_6 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, c.val = 1) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      (∃ k : ℕ, target.val ≤ ((coins.val.length : ℤ) + 1) * 2 ^ k - 1 ∧
        (∀ k' : ℕ, target.val ≤ ((coins.val.length : ℤ) + 1) * 2 ^ k' - 1 → k ≤ k') ∧
        r.val = (k : ℤ)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, c.val = 1), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      (∃ k : ℕ, target.val ≤ ((coins.val.length : ℤ) + 1) * 2 ^ k - 1 ∧
        (∀ k' : ℕ, target.val ≤ ((coins.val.length : ℤ) + 1) * 2 ^ k' - 1 → k ≤ k') ∧
        r.val = (k : ℤ))) := by
  sorry

/-- Let r1 be the result of minimum_added_coins(coins, T1) and let r2 be the result of minimum_added_coins(coins, T2). The function returns these results and r1 <= r2.
  Preconditions: T1 and T2 are integers with 1 <= T1 <= T2 <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= T1. -/
theorem spec_7 (coins : Slice Std.I64) (T1 T2 : Std.I64)
    (hT1a : 1 ≤ T1.val) (hT12 : T1.val ≤ T2.val) (hT2 : T2.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ T1.val) :
    ∃ r1 r2 : Std.I64,
      minimum_added_coins coins T1 = ok r1 ∧ minimum_added_coins coins T2 = ok r2 ∧
        r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (coins : Slice Std.I64) (T1 T2 : Std.I64)
    (hT1a : 1 ≤ T1.val) (hT12 : T1.val ≤ T2.val) (hT2 : T2.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ T1.val), ∃ r1 r2 : Std.I64,
      minimum_added_coins coins T1 = ok r1 ∧ minimum_added_coins coins T2 = ok r2 ∧
        r1.val ≤ r2.val) := by
  sorry

/-- Let r be the result for coins and let r' be the result for coins'. The function returns these results and r' <= r.
  Preconditions: target T has 1 <= T <= 100000; coins and coins' are slices of length between 1 and 100000; all entries of both slices lie in [1,T]; len(coins) < 100000; coins' is obtained from coins by inserting one additional value v with 1 <= v <= T at any position. -/
theorem spec_8 (coins coins' : Slice Std.I64) (T : Std.I64)
    (hT1 : 1 ≤ T.val) (hT2 : T.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn1' : 1 ≤ coins'.val.length)
    (hn2 : coins.val.length < 100000) (hn2' : coins'.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hc' : ∀ c ∈ coins'.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hins : ∃ (v : Std.I64) (l₁ l₂ : List Std.I64),
      coins.val = l₁ ++ l₂ ∧ coins'.val = l₁ ++ [v] ∧ 1 ≤ v.val ∧ v.val ≤ T.val) :
    ∃ r r' : Std.I64,
      minimum_added_coins coins T = ok r ∧ minimum_added_coins coins' T = ok r' ∧
        r'.val ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (coins coins' : Slice Std.I64) (T : Std.I64)
    (hT1 : 1 ≤ T.val) (hT2 : T.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn1' : 1 ≤ coins'.val.length)
    (hn2 : coins.val.length < 100000) (hn2' : coins'.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hc' : ∀ c ∈ coins'.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hins : ∃ (v : Std.I64) (l₁ l₂ : List Std.I64),
      coins.val = l₁ ++ l₂ ∧ coins'.val = l₁ ++ [v] ∧ 1 ≤ v.val ∧ v.val ≤ T.val), ∃ r r' : Std.I64,
      minimum_added_coins coins T = ok r ∧ minimum_added_coins coins' T = ok r' ∧
        r'.val ≤ r.val) := by
  sorry

/-- The two calls minimum_added_coins(coins, T) and minimum_added_coins(coins', T) return the same value r.
  Preconditions: target T has 1 <= T <= 100000; coins and coins' are slices of length n with 1 <= n <= 100000; all entries of both slices lie in [1,T]; coins' is a permutation of coins, meaning the two slices have the same multiset of values. -/
theorem spec_9 (coins coins' : Slice Std.I64) (T : Std.I64)
    (hT1 : 1 ≤ T.val) (hT2 : T.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hn1' : 1 ≤ coins'.val.length) (hn2' : coins'.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hc' : ∀ c ∈ coins'.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hperm : coins'.val.Perm coins.val) :
    ∃ r : Std.I64, minimum_added_coins coins T = ok r ∧ minimum_added_coins coins' T = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (coins coins' : Slice Std.I64) (T : Std.I64)
    (hT1 : 1 ≤ T.val) (hT2 : T.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hn1' : 1 ≤ coins'.val.length) (hn2' : coins'.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hc' : ∀ c ∈ coins'.val, 1 ≤ c.val ∧ c.val ≤ T.val)
    (hperm : coins'.val.Perm coins.val), ∃ r : Std.I64, minimum_added_coins coins T = ok r ∧ minimum_added_coins coins' T = ok r) := by
  sorry

/-- Let r be the returned value. For every finite list A of length r of positive integers such that the multiset consisting of all coins[i] together with all A[j] makes every integer in [1,target] obtainable, every entry A[j] satisfies 1 <= A[j] <= target.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_10 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      ∀ A : List ℤ, (A.length : ℤ) = r.val → (∀ a ∈ A, 1 ≤ a) →
        CoversUpTo (coinVals coins) A target.val → ∀ a ∈ A, 1 ≤ a ∧ a ≤ target.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      ∀ A : List ℤ, (A.length : ℤ) = r.val → (∀ a ∈ A, 1 ≤ a) →
        CoversUpTo (coinVals coins) A target.val → ∀ a ∈ A, 1 ≤ a ∧ a ≤ target.val) := by
  sorry

/-- Let r be the returned value. For every finite list A of length r of positive integers such that coins together with A makes every integer in [1,target] obtainable, and for every integer v with 1 <= v <= target, the sum of all coins[i] with coins[i] <= v plus the sum of all A[j] with A[j] <= v is at least v.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_11 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      ∀ A : List ℤ, (A.length : ℤ) = r.val → (∀ a ∈ A, 1 ≤ a) →
        CoversUpTo (coinVals coins) A target.val →
          ∀ v : ℤ, 1 ≤ v → v ≤ target.val → v ≤ sumLE (coinVals coins) v + sumLE A v := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      ∀ A : List ℤ, (A.length : ℤ) = r.val → (∀ a ∈ A, 1 ≤ a) →
        CoversUpTo (coinVals coins) A target.val →
          ∀ v : ℤ, 1 ≤ v → v ≤ target.val → v ≤ sumLE (coinVals coins) v + sumLE A v) := by
  sorry

/-- Let r be the returned value. For every finite list A of positive integers such that coins together with A makes every integer in [1,target] obtainable, there exists an index j with A[j] = 1.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 2 <= coins[i] <= target. -/
theorem spec_12 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 2 ≤ c.val ∧ c.val ≤ target.val) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      ∀ A : List ℤ, (∀ a ∈ A, 1 ≤ a) → CoversUpTo (coinVals coins) A target.val → 1 ∈ A := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 2 ≤ c.val ∧ c.val ≤ target.val), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      ∀ A : List ℤ, (∀ a ∈ A, 1 ≤ a) → CoversUpTo (coinVals coins) A target.val → 1 ∈ A) := by
  sorry

/-- Let the entries of coins be sorted in nondecreasing order. Initialize R = 0 and c = 0. For each coin value v in the sorted order, while v > R + 1, set R = 2R + 1 and increment c; then set R = R + v. After all coins have been processed, while R < target, set R = 2R + 1 and increment c. The function returns c.
  Preconditions: target is an integer with 1 <= target <= 100000; coins has length n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= coins[i] <= target. -/
theorem spec_13 (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val)
    (hsorted : coins.val.Pairwise (fun a b => a.val ≤ b.val)) :
    ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      r.val = greedyValue (coinVals coins) target.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (coins : Slice Std.I64) (target : Std.I64)
    (hT1 : 1 ≤ target.val) (hT2 : target.val ≤ 100000)
    (hn1 : 1 ≤ coins.val.length) (hn2 : coins.val.length ≤ 100000)
    (hc : ∀ c ∈ coins.val, 1 ≤ c.val ∧ c.val ≤ target.val)
    (hsorted : coins.val.Pairwise (fun a b => a.val ≤ b.val)), ∃ r : Std.I64, minimum_added_coins coins target = ok r ∧
      r.val = greedyValue (coinVals coins) target.val) := by
  sorry

end AegisSpec.MinimumAddedCoins
