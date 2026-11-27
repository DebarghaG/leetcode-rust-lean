import Aegis.MinMoves.Code.Funs

/-!
# Specifications of `Aegis.MinMoves.min_moves`

LeetCode problem `minimum-adjacent-swaps-for-k-consecutive-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinMoves

def absSub (a b : ℤ) : ℤ := if a ≤ b then b - a else a - b

def numOnes : List I64 → ℕ
  | [] => 0
  | x :: xs => (if x.val = 1 then 1 else 0) + numOnes xs

def onePositionsAux : List I64 → ℕ → List ℕ
  | [], _ => []
  | x :: xs, i =>
      if x.val = 1 then i :: onePositionsAux xs (i + 1) else onePositionsAux xs (i + 1)

def onePositions (l : List I64) : List ℕ := onePositionsAux l 0

def IsBinary (l : List I64) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), (l.get ⟨i, hi⟩).val = 0 ∨ (l.get ⟨i, hi⟩).val = 1

def HasRunOfOnes (l : List I64) (k : ℕ) : Prop :=
  ∃ (s : ℕ) (hs : s + k ≤ l.length), ∀ (j : ℕ) (_hj : j < k), (l.get ⟨s + j, by omega⟩).val = 1

def windowOnes (l : List I64) (k s : ℕ) : ℕ := numOnes ((l.drop s).take k)

def maxWindowOnes (l : List I64) (k : ℕ) : ℕ :=
  ((List.range (l.length + 1 - k)).map (fun s => windowOnes l k s)).foldr max 0

def swapCost (p q : List ℕ) : ℤ :=
  ((p.zip q).map (fun ab => absSub (ab.1 : ℤ) (ab.2 : ℤ))).sum

def IsCandidate (nums b : List I64) (k : ℕ) : Prop :=
  b.length = nums.length ∧ IsBinary b ∧
    (onePositions b).length = (onePositions nums).length ∧ HasRunOfOnes b k

def IsAnswer (nums : List I64) (k : ℕ) (r : ℤ) : Prop :=
  (∀ b : List I64, IsCandidate nums b k →
      r ≤ swapCost (onePositions nums) (onePositions b)) ∧
    (∃ b : List I64,
      IsCandidate nums b k ∧ swapCost (onePositions nums) (onePositions b) = r)

def consecutiveGaps (p : List ℕ) : List ℕ :=
  (p.zip (p.drop 1)).map (fun ab => ab.2 - ab.1 - 1)

def listMin : List ℕ → ℕ
  | [] => 0
  | [a] => a
  | a :: b :: rest => min a (listMin (b :: rest))

def listMinZ : List ℤ → ℤ
  | [] => 0
  | [a] => a
  | a :: b :: rest => min a (listMinZ (b :: rest))

def blockCostAt (p : List ℕ) (k l s : ℕ) : ℤ :=
  ((List.range k).map (fun j => absSub (p.getD (l + j) 0 : ℤ) (s + j : ℤ))).sum

def minRunCost (p : List ℕ) (n k : ℕ) : ℤ :=
  listMinZ ((List.range (n + 1 - k)).map (fun s => blockCostAt p k 0 s))

def shiftedAt (p : List ℕ) (l j : ℕ) : ℤ := (p.getD (l + j) 0 : ℤ) - (j : ℤ)

def medianCost (p : List ℕ) (k l : ℕ) (med : ℤ) : ℤ :=
  ((List.range k).map (fun j => absSub (shiftedAt p l j) med)).sum

def dropLeadingZeros : List I64 → List I64
  | [] => []
  | x :: xs => if x.val = 0 then dropLeadingZeros xs else x :: xs

def dropTrailingZeros (l : List I64) : List I64 := (dropLeadingZeros l.reverse).reverse

def coreOf (l : List I64) : List I64 := dropTrailingZeros (dropLeadingZeros l)

/-- The function returns a result r (it does not fail) and r is the minimum, over all binary arrays b of length n that contain exactly m ones and have k consecutive ones (there exists s with 0 <= s <= n-k such that b[s] = b[s+1] = ... = b[s+k-1] = 1), of the adjacent-swap distance D(nums,b). Here, if p_0 < p_1 < ... < p_{m-1} are the indices with nums[p_j] = 1 and q_0 < q_1 < ... < q_{m-1} are the indices with b[q_j] = 1, then D(nums,b) = sum_{j=0}^{m-1} |p_j - q_j|. Equivalently, r = min { D(nums,b) : b is a binary array of length n with exactly m ones and with k consecutive ones }.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= m, where m is the number of indices i with nums[i] = 1. Let n = len(nums). -/
theorem spec_1 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∃ r : I64, Aegis.MinMoves.min_moves nums k = ok r ∧ IsAnswer nums.val k.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∃ r : I64, Aegis.MinMoves.min_moves nums k = ok r ∧ IsAnswer nums.val k.val.toNat r.val) := by
  sorry

/-- For every valid input, the function returns a result r; it does not panic, overflow, or access an index outside the slice.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_2 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∃ r : I64, Aegis.MinMoves.min_moves nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∃ r : I64, Aegis.MinMoves.min_moves nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_3 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= k * len(nums).
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_4 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64,
      Aegis.MinMoves.min_moves nums k = ok r → r.val ≤ k.val * (nums.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64,
      Aegis.MinMoves.min_moves nums k = ok r → r.val ≤ k.val * (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let M = max { c(s) : 0 <= s <= n-k }, where c(s) is the number of indices i with s <= i < s+k and nums[i] = 1. Then r >= k - M.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. Let n = len(nums). -/
theorem spec_5 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      k.val - ((maxWindowOnes nums.val k.val.toNat : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      k.val - ((maxWindowOnes nums.val k.val.toNat : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists an integer s with 0 <= s <= len(nums)-k such that nums[s] = nums[s+1] = ... = nums[s+k-1] = 1.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_6 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      (r.val = 0 ↔ HasRunOfOnes nums.val k.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      (r.val = 0 ↔ HasRunOfOnes nums.val k.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and k = 1, with 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_7 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ))
    (hk : k.val = 1) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ))
    (hk : k.val = 1), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if p_0 < p_1 < ... < p_{m-1} are all indices with nums[p_j] = 1, so m >= 2, then r = min { p_{i+1} - p_i - 1 : 0 <= i < m-1 }.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and k = 2, with 2 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_8 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ))
    (hk : k.val = 2) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      r.val = ((listMin (consecutiveGaps (onePositions nums.val)) : ℕ) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ))
    (hk : k.val = 2), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      r.val = ((listMin (consecutiveGaps (onePositions nums.val)) : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = min { sum_{j=0}^{k-1} |p_j - (s+j)| : 0 <= s <= n-k }.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and k equals the number of indices i with nums[i] = 1. Let n = len(nums) and let p_0 < p_1 < ... < p_{k-1} be all one-indices. -/
theorem spec_9 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ))
    (hk : k.val = ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      r.val = minRunCost (onePositions nums.val) nums.val.length k.val.toNat := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ))
    (hk : k.val = ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      r.val = minRunCost (onePositions nums.val) nums.val.length k.val.toNat) := by
  sorry

/-- Let n = len(nums), and let rev be the sequence of length n defined by rev[i] = nums[n-1-i] for 0 <= i < n. Whenever the function returns r for nums, the exact answer for input (rev,k), defined by the same minimization as spec_1 with rev in place of nums, is also r.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_10 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      IsAnswer nums.val.reverse k.val.toNat r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      IsAnswer nums.val.reverse k.val.toNat r.val) := by
  sorry

/-- Let core be obtained from nums by deleting all leading zeros and all trailing zeros. Whenever the function returns r for nums, the exact answer for input (core,k), defined by the same minimization as spec_1 with core in place of nums, is also r.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= the number of indices i with nums[i] = 1. -/
theorem spec_11 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      IsAnswer (coreOf nums.val) k.val.toNat r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      IsAnswer (coreOf nums.val) k.val.toNat r.val) := by
  sorry

/-- Whenever the function returns r for parameter k, r <= R, where R is the exact minimum number of moves for the same nums and parameter k+1, defined by the main specification with k+1.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and k+1 <= the number of indices i with nums[i] = 1. -/
theorem spec_12 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm1 : k.val + 1 ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ (r : I64) (R : ℤ), Aegis.MinMoves.min_moves nums k = ok r →
      IsAnswer nums.val (k.val.toNat + 1) R → r.val ≤ R := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm1 : k.val + 1 ≤ ((onePositions nums.val).length : ℤ)), ∀ (r : I64) (R : ℤ), Aegis.MinMoves.min_moves nums k = ok r →
      IsAnswer nums.val (k.val.toNat + 1) R → r.val ≤ R) := by
  sorry

/-- Whenever the function returns r, there exist integers l and s with 0 <= l <= m-k and 0 <= s <= n-k such that r = sum_{j=0}^{k-1} |p_{l+j} - (s+j)|, and for every l' with 0 <= l' <= m-k and every s' with 0 <= s' <= n-k, sum_{j=0}^{k-1} |p_{l'+j} - (s'+j)| >= r.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] is 0 or 1; and 1 <= k <= m, where m is the number of indices i with nums[i] = 1. Let n = len(nums) and let p_0 < p_1 < ... < p_{m-1} be all one-indices. -/
theorem spec_13 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      ∃ (l s : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length ∧
        s + k.val.toNat ≤ nums.val.length ∧
        r.val = blockCostAt (onePositions nums.val) k.val.toNat l s ∧
        (∀ (l' s' : ℕ), l' + k.val.toNat ≤ (onePositions nums.val).length →
          s' + k.val.toNat ≤ nums.val.length →
          r.val ≤ blockCostAt (onePositions nums.val) k.val.toNat l' s') := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), ∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      ∃ (l s : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length ∧
        s + k.val.toNat ≤ nums.val.length ∧
        r.val = blockCostAt (onePositions nums.val) k.val.toNat l s ∧
        (∀ (l' s' : ℕ), l' + k.val.toNat ≤ (onePositions nums.val).length →
          s' + k.val.toNat ≤ nums.val.length →
          r.val ≤ blockCostAt (onePositions nums.val) k.val.toNat l' s')) := by
  sorry

/-- For each l with 0 <= l <= m-k, define a_j = p_{l+j} - j for 0 <= j < k; these a_j are nondecreasing. Let med_l be any integer satisfying a_{floor((k-1)/2)} <= med_l <= a_{ceil((k-1)/2)}. Then whenever the function returns r, r = min { sum_{j=0}^{k-1} |a_j - med_l| : 0 <= l <= m-k }.
  Preconditions: Valid input: 1 <= len(nums) <= 100000; every nums[i] is 0 or 1; 1 <= k <= m, where m is the number of ones. Let n = len(nums) and let p_0 < p_1 < ... < p_{m-1} be all one-indices. -/
theorem spec_14 (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)) :
    (∀ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length →
      ∀ (j j' : ℕ), j ≤ j' → j' < k.val.toNat →
        shiftedAt (onePositions nums.val) l j ≤ shiftedAt (onePositions nums.val) l j') ∧
    (∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      ∀ med : ℕ → ℤ,
        (∀ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length →
          shiftedAt (onePositions nums.val) l ((k.val.toNat - 1) / 2) ≤ med l ∧
            med l ≤ shiftedAt (onePositions nums.val) l (k.val.toNat / 2)) →
        (∀ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length →
          r.val ≤ medianCost (onePositions nums.val) k.val.toNat l (med l)) ∧
        (∃ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length ∧
          medianCost (onePositions nums.val) k.val.toNat l (med l) = r.val)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hlen : 1 ≤ nums.val.length)
    (hlenb : nums.val.length ≤ 100000) (hbin : IsBinary nums.val)
    (hk1 : 1 ≤ k.val) (hkm : k.val ≤ ((onePositions nums.val).length : ℤ)), (∀ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length →
      ∀ (j j' : ℕ), j ≤ j' → j' < k.val.toNat →
        shiftedAt (onePositions nums.val) l j ≤ shiftedAt (onePositions nums.val) l j') ∧
    (∀ r : I64, Aegis.MinMoves.min_moves nums k = ok r →
      ∀ med : ℕ → ℤ,
        (∀ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length →
          shiftedAt (onePositions nums.val) l ((k.val.toNat - 1) / 2) ≤ med l ∧
            med l ≤ shiftedAt (onePositions nums.val) l (k.val.toNat / 2)) →
        (∀ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length →
          r.val ≤ medianCost (onePositions nums.val) k.val.toNat l (med l)) ∧
        (∃ (l : ℕ), l + k.val.toNat ≤ (onePositions nums.val).length ∧
          medianCost (onePositions nums.val) k.val.toNat l (med l) = r.val))) := by
  sorry

end AegisSpec.MinMoves
