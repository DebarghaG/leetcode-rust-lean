import Aegis.MaxCoins.Code.Funs

/-!
# Specifications of `Aegis.MaxCoins.max_coins`

LeetCode problem `burst-balloons`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxCoins

namespace AegisSpec.MaxCoins

def entries (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def ith (a : List ℤ) (i : ℕ) : ℤ := a.getD i 0

def InRange (a : List ℤ) (n : ℕ) : Prop := ∀ i, i < n → 0 ≤ ith a i ∧ ith a i ≤ 100

def listMax (a : List ℤ) : ℤ := (a.max?).getD 0

def predIdx (rem : List ℕ) (k : ℕ) : Option ℕ :=
  rem.foldr
    (fun j acc => if j < k then some (match acc with | none => j | some m => max j m) else acc)
    none

def succIdx (rem : List ℕ) (k : ℕ) : Option ℕ :=
  rem.foldr
    (fun j acc => if k < j then some (match acc with | none => j | some m => min j m) else acc)
    none

def leftNeighbour (a : List ℤ) (rem : List ℕ) (k : ℕ) : ℤ :=
  match predIdx rem k with
  | none => 1
  | some j => a.getD j 1

def rightNeighbour (a : List ℤ) (rem : List ℕ) (k : ℕ) : ℤ :=
  match succIdx rem k with
  | none => 1
  | some j => a.getD j 1

def burstTotal (a : List ℤ) (p : List ℕ) : ℤ :=
  (List.range p.length).foldl
    (fun acc k =>
      acc +
        leftNeighbour a (p.drop k) (p.getD k 0) * a.getD (p.getD k 0) 1 *
          rightNeighbour a (p.drop k) (p.getD k 0))
    (0 : ℤ)

def bestTotal (a : List ℤ) : ℤ :=
  match (List.range a.length).permutations.map (burstTotal a) with
  | [] => 0
  | t :: ts => ts.foldl max t

/-- A burst order is a permutation p of {0,...,n-1}, written p[0],...,p[n-1] in the order the balloons are burst. For 0 <= k < n let remaining_k = {p[k], p[k+1], ..., p[n-1]}. Define left_k = nums[j] for the largest j in remaining_k with j < p[k], and left_k = 1 if no such j exists. Define right_k = nums[j] for the smallest j in remaining_k with j > p[k], and right_k = 1 if no such j exists. Let total(p) = sum_{k=0}^{n-1} left_k * nums[p[k]] * right_k. Then max_coins(nums) returns a result r and r = max { total(p) : p is a permutation of {0,...,n-1} }.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    ∃ r : I64, max_coins nums = ok r ∧ r.val = bestTotal (entries nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), ∃ r : I64, max_coins nums = ok r ∧ r.val = bestTotal (entries nums)) := by
  sorry

/-- For every nums satisfying these preconditions, max_coins(nums) returns a result r and does not fail by panic, out-of-bounds access, or 64-bit arithmetic overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    ∃ r : I64, max_coins nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), ∃ r : I64, max_coins nums = ok r) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r >= sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    max_coins nums = ok r → (entries nums).sum ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), max_coins nums = ok r → (entries nums).sum ≤ r.val) := by
  sorry

/-- Let M = max_{0 <= i < n} nums[i] and S = sum_{i=0}^{n-1} nums[i]. Whenever max_coins(nums) returns a result r, r <= M^2 * S.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    max_coins nums = ok r → r.val ≤ listMax (entries nums) ^ 2 * (entries nums).sum := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), max_coins nums = ok r → r.val ≤ listMax (entries nums) ^ 2 * (entries nums).sum) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r >= max { nums[i] * nums[j] : 0 <= i < j < n }.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn2 : 2 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    max_coins nums = ok r →
      ∀ i j : ℕ, i < j → j < n → ith (entries nums) i * ith (entries nums) j ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn2 : 2 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), max_coins nums = ok r →
      ∀ i j : ℕ, i < j → j < n → ith (entries nums) i * ith (entries nums) j ≤ r.val) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r >= max { nums[i] * nums[j] * nums[k] : 0 <= i < j < k < n }.
  Preconditions: Let n = len(nums). Assume 3 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn3 : 3 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    max_coins nums = ok r → ∀ i j k : ℕ, i < j → j < k → k < n →
      ith (entries nums) i * ith (entries nums) j * ith (entries nums) k ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn3 : 3 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), max_coins nums = ok r → ∀ i j k : ℕ, i < j → j < k → k < n →
      ith (entries nums) i * ith (entries nums) j * ith (entries nums) k ≤ r.val) := by
  sorry

/-- Whenever max_coins(a) returns a result r_a and max_coins(b) returns a result r_b, r_a <= r_b.
  Preconditions: Let a and b be slices of the same length n with 1 <= n <= 300, and for every i with 0 <= i < n, 0 <= a[i] <= b[i] <= 100. -/
theorem spec_7 (a b : Slice I64) (ra rb : I64) (n : ℕ) (hna : n = (entries a).length)
    (hnb : n = (entries b).length) (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : ∀ i, i < n → 0 ≤ ith (entries a) i ∧ ith (entries a) i ≤ ith (entries b) i ∧
      ith (entries b) i ≤ 100) :
    max_coins a = ok ra → max_coins b = ok rb → ra.val ≤ rb.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b : Slice I64) (ra rb : I64) (n : ℕ) (hna : n = (entries a).length)
    (hnb : n = (entries b).length) (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : ∀ i, i < n → 0 ≤ ith (entries a) i ∧ ith (entries a) i ≤ ith (entries b) i ∧
      ith (entries b) i ≤ 100), max_coins a = ok ra → max_coins b = ok rb → ra.val ≤ rb.val) := by
  sorry

/-- Let rev be the slice of length n defined by rev[i] = nums[n-1-i] for 0 <= i < n. Whenever max_coins(nums) returns a result r and max_coins(rev) returns a result r_rev, r = r_rev.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_8 (nums rev : Slice I64) (r rrev : I64) (n : ℕ)
    (hn : n = (entries nums).length) (hnrev : n = (entries rev).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n)
    (hrev : ∀ i, i < n → ith (entries rev) i = ith (entries nums) (n - 1 - i)) :
    max_coins nums = ok r → max_coins rev = ok rrev → r.val = rrev.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums rev : Slice I64) (r rrev : I64) (n : ℕ)
    (hn : n = (entries nums).length) (hnrev : n = (entries rev).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n)
    (hrev : ∀ i, i < n → ith (entries rev) i = ith (entries nums) (n - 1 - i)), max_coins nums = ok r → max_coins rev = ok rrev → r.val = rrev.val) := by
  sorry

/-- Let pos be the subsequence of nums consisting exactly of the entries nums[i] with nums[i] > 0, in their original order. Whenever max_coins(nums) returns a result r: if pos is empty then r = 0; if pos is nonempty and max_coins(pos) returns a result r_pos, then r = r_pos.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_9 (nums pos : Slice I64) (r rpos : I64) (n : ℕ)
    (hn : n = (entries nums).length) (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : InRange (entries nums) n)
    (hpos : entries pos = (entries nums).filter (fun x => decide (0 < x))) :
    max_coins nums = ok r →
      (entries pos = [] → r.val = 0) ∧
        (entries pos ≠ [] → max_coins pos = ok rpos → r.val = rpos.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums pos : Slice I64) (r rpos : I64) (n : ℕ)
    (hn : n = (entries nums).length) (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : InRange (entries nums) n)
    (hpos : entries pos = (entries nums).filter (fun x => decide (0 < x))), max_coins nums = ok r →
      (entries pos = [] → r.val = 0) ∧
        (entries pos ≠ [] → max_coins pos = ok rpos → r.val = rpos.val)) := by
  sorry

/-- Whenever max_coins(nums) returns a result r and max_coins(nums') returns a result r', r' >= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 299, for every i with 0 <= i < n, 0 <= nums[i] <= 100, let x satisfy 0 <= x <= 100, and let k satisfy 0 <= k <= n. Let nums' be the slice of length n+1 obtained by inserting x at position k, so nums'[i] = nums[i] for i < k, nums'[k] = x, and nums'[i] = nums[i-1] for i > k. -/
theorem spec_10 (nums nums' : Slice I64) (r r' : I64) (n k : ℕ) (x : I64)
    (hn : n = (entries nums).length) (hn1 : 1 ≤ n) (hn299 : n ≤ 299)
    (hb : InRange (entries nums) n) (hx0 : 0 ≤ x.val) (hx100 : x.val ≤ 100) (hk : k ≤ n)
    (hnums' : entries nums' =
      (entries nums).take k ++ [x.val] ++ (entries nums).drop k) :
    max_coins nums = ok r → max_coins nums' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice I64) (r r' : I64) (n k : ℕ) (x : I64)
    (hn : n = (entries nums).length) (hn1 : 1 ≤ n) (hn299 : n ≤ 299)
    (hb : InRange (entries nums) n) (hx0 : 0 ≤ x.val) (hx100 : x.val ≤ 100) (hk : k ≤ n)
    (hnums' : entries nums' =
      (entries nums).take k ++ [x.val] ++ (entries nums).drop k), max_coins nums = ok r → max_coins nums' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r = nums[0].
  Preconditions: len(nums) = 1 and 0 <= nums[0] <= 100. -/
theorem spec_11 (nums : Slice I64) (r : I64) (hlen : (entries nums).length = 1)
    (hb : 0 ≤ ith (entries nums) 0 ∧ ith (entries nums) 0 ≤ 100) :
    max_coins nums = ok r → r.val = ith (entries nums) 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hlen : (entries nums).length = 1)
    (hb : 0 ≤ ith (entries nums) 0 ∧ ith (entries nums) 0 ≤ 100), max_coins nums = ok r → r.val = ith (entries nums) 0) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r = sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
theorem spec_12 (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : ∀ i, i < n → ith (entries nums) i = 0 ∨ ith (entries nums) i = 1) :
    max_coins nums = ok r → r.val = (entries nums).sum := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : ∀ i, i < n → ith (entries nums) i = 0 ∨ ith (entries nums) i = 1), max_coins nums = ok r → r.val = (entries nums).sum) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r = nums[k].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300, for every i with 0 <= i < n, 0 <= nums[i] <= 100, and there exists exactly one index k with 0 <= k < n such that nums[k] > 0. -/
theorem spec_13 (nums : Slice I64) (r : I64) (n k : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) (hk : k < n)
    (hpos : 0 < ith (entries nums) k) (huniq : ∀ j, j < n → 0 < ith (entries nums) j → j = k) :
    max_coins nums = ok r → r.val = ith (entries nums) k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n k : ℕ) (hn : n = (entries nums).length)
    (hn1 : 1 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) (hk : k < n)
    (hpos : 0 < ith (entries nums) k) (huniq : ∀ j, j < n → 0 < ith (entries nums) j → j = k), max_coins nums = ok r → r.val = ith (entries nums) k) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r = a * b + max(a, b).
  Preconditions: len(nums) = 2, nums[0] = a, nums[1] = b, and 0 <= a <= 100, 0 <= b <= 100. -/
theorem spec_14 (nums : Slice I64) (r : I64) (a b : ℤ) (hlen : (entries nums).length = 2)
    (h0 : ith (entries nums) 0 = a) (h1 : ith (entries nums) 1 = b)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 100) (hb0 : 0 ≤ b) (hb1 : b ≤ 100) :
    max_coins nums = ok r → r.val = a * b + max a b := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (a b : ℤ) (hlen : (entries nums).length = 2)
    (h0 : ith (entries nums) 0 = a) (h1 : ith (entries nums) 1 = b)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 100) (hb0 : 0 ≤ b) (hb1 : b ≤ 100), max_coins nums = ok r → r.val = a * b + max a b) := by
  sorry

/-- Whenever max_coins(nums) returns a result r, r >= max { nums[i] * nums[j] + max(nums[i], nums[j]) : 0 <= i < j < n }.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. -/
theorem spec_15 (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn2 : 2 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n) :
    max_coins nums = ok r → ∀ i j : ℕ, i < j → j < n →
      ith (entries nums) i * ith (entries nums) j +
        max (ith (entries nums) i) (ith (entries nums) j) ≤ r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (n : ℕ) (hn : n = (entries nums).length)
    (hn2 : 2 ≤ n) (hn300 : n ≤ 300) (hb : InRange (entries nums) n), max_coins nums = ok r → ∀ i j : ℕ, i < j → j < n →
      ith (entries nums) i * ith (entries nums) j +
        max (ith (entries nums) i) (ith (entries nums) j) ≤ r.val) := by
  sorry

/-- Whenever max_coins(nums) returns a result r and max_coins(sub) returns a result r_sub, r >= r_sub.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 300 and for every i with 0 <= i < n, 0 <= nums[i] <= 100. Let sub be a nonempty slice formed by a subsequence of nums in the same order, so len(sub) >= 1. -/
theorem spec_16 (nums sub : Slice I64) (r rsub : I64) (n : ℕ)
    (hn : n = (entries nums).length) (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : InRange (entries nums) n) (hsub : List.Sublist (entries sub) (entries nums))
    (hne : entries sub ≠ []) :
    max_coins nums = ok r → max_coins sub = ok rsub → rsub.val ≤ r.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums sub : Slice I64) (r rsub : I64) (n : ℕ)
    (hn : n = (entries nums).length) (hn1 : 1 ≤ n) (hn300 : n ≤ 300)
    (hb : InRange (entries nums) n) (hsub : List.Sublist (entries sub) (entries nums))
    (hne : entries sub ≠ []), max_coins nums = ok r → max_coins sub = ok rsub → rsub.val ≤ r.val) := by
  sorry

end AegisSpec.MaxCoins
