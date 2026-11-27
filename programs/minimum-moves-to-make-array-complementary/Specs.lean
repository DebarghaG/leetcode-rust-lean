import Aegis.MinMoves.Code.Funs

/-!
# Specifications of `Aegis.MinMoves.min_moves`

LeetCode problem `minimum-moves-to-make-array-complementary`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinMoves

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def len (nums : Slice Std.I64) : Nat := (vals nums).length

def Feasible (n : Nat) (limit : Int) (b : List Int) (s : Int) : Prop :=
  b.length = n ∧
    (∀ j, j < n → 1 ≤ b.getD j 0 ∧ b.getD j 0 ≤ limit) ∧
    (∀ i, i < n → b.getD i 0 + b.getD (n - 1 - i) 0 = s)

def diffCount (n : Nat) (a b : List Int) : Nat :=
  ((List.range n).filter (fun j => a.getD j 0 ≠ b.getD j 0)).length

def Achievable (n : Nat) (limit : Int) (a : List Int) (m : Int) : Prop :=
  0 ≤ m ∧ ∃ (s : Int) (b : List Int), Feasible n limit b s ∧ (diffCount n a b : Int) = m

def pairCost (limit a b s : Int) : Nat :=
  if a + b = s then 0
  else if (1 ≤ s - a ∧ s - a ≤ limit) ∨ (1 ≤ s - b ∧ s - b ≤ limit) then 1
  else 2

def totalCost (nums : Slice Std.I64) (limit S : Int) : Int :=
  ((List.range (len nums / 2)).map
    (fun i => (pairCost limit (entry nums i) (entry nums (len nums - 1 - i)) S : Int))).sum

def nonCentralCount (nums : Slice Std.I64) (limit : Int) : Nat :=
  ((List.range (len nums / 2)).filter
    (fun i => entry nums i + entry nums (len nums - 1 - i) ≠ limit + 1)).length

def swapAt (l : List Int) (i j : Nat) : List Int :=
  (List.range l.length).map
    (fun k => if k = i then l.getD j 0 else if k = j then l.getD i 0 else l.getD k 0)

def permutePairs (l : List Int) (m : Nat) (π : Nat → Nat) : List Int :=
  (List.range (2 * m)).map
    (fun k =>
      if k < m then l.getD (π k) 0
      else l.getD (2 * m - 1 - π (2 * m - 1 - k)) 0)

/-- Whenever the function returns a result r, r is the smallest nonnegative integer m for which there exist an integer s and an array b of length n such that: (1) 1 ≤ b[j] ≤ limit for every j with 0 ≤ j < n; (2) b[i] + b[n-1-i] = s for every i with 0 ≤ i < n; and (3) m equals the number of indices j with 0 ≤ j < n for which b[j] ≠ nums[j].
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_1 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r) :
    Achievable (len nums) limit.val (vals nums) r.val ∧
      ∀ m : Int, Achievable (len nums) limit.val (vals nums) m → r.val ≤ m := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r), Achievable (len nums) limit.val (vals nums) r.val ∧
      ∀ m : Int, Achievable (len nums) limit.val (vals nums) m → r.val ≤ m) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access outside the slice.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_2 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val) :
    ∃ r : Std.I64, Aegis.MinMoves.min_moves nums limit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val), ∃ r : Std.I64, Aegis.MinMoves.min_moves nums limit = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 ≤ r ≤ n/2, where n = len(nums) and n/2 is an integer because n is even.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_3 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((len nums / 2 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r), 0 ≤ r.val ∧ r.val ≤ ((len nums / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if nums is already complementary, meaning there exists an integer S such that nums[i] + nums[n-1-i] = S for every i with 0 ≤ i < n.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_4 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r) :
    r.val = 0 ↔ ∃ S : Int, ∀ i, i < len nums → entry nums i + entry nums (len nums - 1 - i) = S := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r), r.val = 0 ↔ ∃ S : Int, ∀ i, i < len nums → entry nums i + entry nums (len nums - 1 - i) = S) := by
  sorry

/-- Define c(a,b,s) for integers a,b,s with 1 ≤ a,b ≤ limit and 2 ≤ s ≤ 2*limit to be 0 if a+b = s; 1 if a+b ≠ s and (1 ≤ s-a ≤ limit or 1 ≤ s-b ≤ limit); and 2 otherwise. Whenever the function returns a result r, there exists an integer S with 2 ≤ S ≤ 2*limit such that r = Σ_{i=0}^{n/2-1} c(nums[i], nums[n-1-i], S).
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_5 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r) :
    ∃ S : Int, 2 ≤ S ∧ S ≤ 2 * limit.val ∧ r.val = totalCost nums limit.val S := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r), ∃ S : Int, 2 ≤ S ∧ S ≤ 2 * limit.val ∧ r.val = totalCost nums limit.val S) := by
  sorry

/-- Define c(a,b,s) for integers a,b,s with 1 ≤ a,b ≤ limit and 2 ≤ s ≤ 2*limit to be 0 if a+b = s; 1 if a+b ≠ s and (1 ≤ s-a ≤ limit or 1 ≤ s-b ≤ limit); and 2 otherwise. Whenever the function returns a result r, for every integer S with 2 ≤ S ≤ 2*limit we have r ≤ Σ_{i=0}^{n/2-1} c(nums[i], nums[n-1-i], S).
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_6 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r) :
    ∀ S : Int, 2 ≤ S → S ≤ 2 * limit.val → r.val ≤ totalCost nums limit.val S := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r), ∀ S : Int, 2 ≤ S → S ≤ 2 * limit.val → r.val ≤ totalCost nums limit.val S) := by
  sorry

/-- Whenever the function returns a result r, r ≤ the number of indices i with 0 ≤ i < n/2 for which nums[i] + nums[n-1-i] ≠ limit + 1.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_7 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r) :
    r.val ≤ (nonCentralCount nums limit.val : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (r : Std.I64) (hr : Aegis.MinMoves.min_moves nums limit = ok r), r.val ≤ (nonCentralCount nums limit.val : Int)) := by
  sorry

/-- Let rev be the array of length n defined by rev[j] = nums[n-1-j] for 0 ≤ j < n. Whenever the function returns r for (nums, limit) and returns r' for (rev, limit), we have r' = r.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_8 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (rev : Slice Std.I64) (hrev : vals rev = (vals nums).reverse)
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves rev limit = ok r') :
    r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (rev : Slice Std.I64) (hrev : vals rev = (vals nums).reverse)
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves rev limit = ok r'), r' = r) := by
  sorry

/-- For any index i with 0 ≤ i < n/2, let nums' be the array obtained from nums by swapping nums[i] and nums[n-1-i] and leaving all other entries unchanged. Whenever the function returns r for (nums, limit) and returns r' for (nums', limit), we have r' = r.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_9 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (i : Nat) (hi : i < len nums / 2)
    (nums' : Slice Std.I64)
    (hnums' : vals nums' = swapAt (vals nums) i (len nums - 1 - i))
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves nums' limit = ok r') :
    r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (i : Nat) (hi : i < len nums / 2)
    (nums' : Slice Std.I64)
    (hnums' : vals nums' = swapAt (vals nums) i (len nums - 1 - i))
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves nums' limit = ok r'), r' = r) := by
  sorry

/-- Let m = n/2, and let π be any permutation of the set {0,1,...,m-1}. Define nums' of length n by nums'[i] = nums[π(i)] and nums'[n-1-i] = nums[n-1-π(i)] for every i with 0 ≤ i < m. Whenever the function returns r for (nums, limit) and returns r' for (nums', limit), we have r' = r.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_10 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (π : Nat → Nat)
    (hπ_lt : ∀ i, i < len nums / 2 → π i < len nums / 2)
    (hπ_inj : ∀ i j, i < len nums / 2 → j < len nums / 2 → π i = π j → i = j)
    (nums' : Slice Std.I64)
    (hnums' : vals nums' = permutePairs (vals nums) (len nums / 2) π)
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves nums' limit = ok r') :
    r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (π : Nat → Nat)
    (hπ_lt : ∀ i, i < len nums / 2 → π i < len nums / 2)
    (hπ_inj : ∀ i j, i < len nums / 2 → j < len nums / 2 → π i = π j → i = j)
    (nums' : Slice Std.I64)
    (hnums' : vals nums' = permutePairs (vals nums) (len nums / 2) π)
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves nums' limit = ok r'), r' = r) := by
  sorry

/-- Whenever the function returns r for (nums, L) and returns r' for (nums, L'), we have r' ≤ r.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, and integers L and L' satisfy 1 ≤ L ≤ L' ≤ 100000 and 1 ≤ nums[i] ≤ L for every i with 0 ≤ i < n. -/
theorem spec_11 (nums : Slice Std.I64) (L L' : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hL_ge : 1 ≤ L.val)
    (hL_le : L.val ≤ L'.val)
    (hL'_le : L'.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ L.val)
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums L = ok r)
    (hr' : Aegis.MinMoves.min_moves nums L' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (L L' : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hL_ge : 1 ≤ L.val)
    (hL_le : L.val ≤ L'.val)
    (hL'_le : L'.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ L.val)
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums L = ok r)
    (hr' : Aegis.MinMoves.min_moves nums L' = ok r'), r'.val ≤ r.val) := by
  sorry

/-- Let nums' be the array of length n defined by nums'[j] = limit + 1 - nums[j] for 0 ≤ j < n. Whenever the function returns r for (nums, limit) and returns r' for (nums', limit), we have r' = r.
  Preconditions: Let n = len(nums). The array nums has even length n with 2 ≤ n ≤ 100000, the integer limit satisfies 1 ≤ limit ≤ 100000, and for every i with 0 ≤ i < n we have 1 ≤ nums[i] ≤ limit. -/
theorem spec_12 (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (nums' : Slice Std.I64)
    (hnums' : vals nums' = (vals nums).map (fun x => limit.val + 1 - x))
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves nums' limit = ok r') :
    r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
    (hn_even : len nums % 2 = 0)
    (hn_ge : 2 ≤ len nums)
    (hn_le : len nums ≤ 100000)
    (hlimit_ge : 1 ≤ limit.val)
    (hlimit_le : limit.val ≤ 100000)
    (hvals : ∀ i, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ limit.val)
    (nums' : Slice Std.I64)
    (hnums' : vals nums' = (vals nums).map (fun x => limit.val + 1 - x))
    (r r' : Std.I64)
    (hr : Aegis.MinMoves.min_moves nums limit = ok r)
    (hr' : Aegis.MinMoves.min_moves nums' limit = ok r'), r' = r) := by
  sorry

end AegisSpec.MinMoves
