import Aegis.UnmarkedSumArray.Code.Funs

/-!
# Specifications of `Aegis.UnmarkedSumArray.unmarked_sum_array`

LeetCode problem `mark-elements-on-array-by-performing-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.UnmarkedSumArray

def numAt (nums : Slice Std.I64) (j : Nat) : Int :=
  match nums.val[j]? with
  | some x => x.val
  | none => 0

def sliceSum (nums : Slice Std.I64) : Int :=
  ((List.range nums.val.length).map (fun j => numAt nums j)).sum

def sumOver (nums : Slice Std.I64) (s : Finset Nat) : Int :=
  s.sum (fun j => numAt nums j)

def precedes (nums : Slice Std.I64) (a b : Nat) : Prop :=
  numAt nums a < numAt nums b ∨ (numAt nums a = numAt nums b ∧ a < b)

instance instDecidablePrecedes (nums : Slice Std.I64) (b : Nat) :
    DecidablePred (fun a => precedes nums a b) :=
  fun a => by unfold precedes; infer_instance

def rank (nums : Slice Std.I64) (U : Finset Nat) (j : Nat) : Nat :=
  (U.filter (fun u => precedes nums u j)).card

def smallest (nums : Slice Std.I64) (U : Finset Nat) (t : Nat) : Finset Nat :=
  U.filter (fun j => rank nums U j < t)

def queryField (queries : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
  (queries.val[i]?).bind (fun v => (v.val[j]?).map (fun x => x.val))

def queryFieldInt (queries : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (queryField queries i j).getD 0

def queryIdx (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  (queryFieldInt queries i 0).toNat

def queryK (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  queryFieldInt queries i 1

def queryLen (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  match queries.val[i]? with
  | some v => v.val.length
  | none => 0

def markedAfter (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64)) :
    Nat → Finset Nat
  | 0 => ∅
  | i + 1 =>
      let M := markedAfter nums queries i
      let A := insert (queryIdx queries i) M
      let U := Finset.range nums.val.length \ A
      A ∪ smallest nums U (min (queryK queries i).toNat U.card)

def markedWithOwn (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (i : Nat) : Finset Nat :=
  insert (queryIdx queries i) (markedAfter nums queries i)

def unmarkedOf (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (i : Nat) : Finset Nat :=
  Finset.range nums.val.length \ markedWithOwn nums queries i

def unmarkedSum (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (i : Nat) : Int :=
  sumOver nums (Finset.range nums.val.length \ markedAfter nums queries i)

def queryIdxSet (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Finset Nat :=
  (Finset.range (i + 1)).image (fun t => queryIdx queries t)

def answerAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Option Int :=
  (r.val[i]?).map (fun x => x.val)

def Answer (r : alloc.vec.Vec Std.I64) (i : Nat) (v : Int) : Prop :=
  answerAt r i = some v

/-- Define M_{-1} = empty set. For 0 <= i < m, let idx_i = queries[i][0], k_i = queries[i][1], A_i = M_{i-1} union {idx_i}, U_i = { j | 0 <= j < n and j not in A_i }, and t_i = min(k_i, |U_i|). Let T_i be the unique subset of U_i with |T_i| = t_i such that for every j in T_i and every u in U_i minus T_i, either nums[j] < nums[u], or nums[j] = nums[u] and j < u. Define M_i = A_i union T_i. Whenever the function returns a result r, len(r) = m and for every i with 0 <= i < m, r[i] = sum over j with 0 <= j < n and j not in M_i of nums[j].
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_1 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    r.val.length = m ∧ ∀ i, i < m → Answer r i (unmarkedSum nums queries (i + 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), r.val.length = m ∧ ∀ i, i < m → Answer r i (unmarkedSum nums queries (i + 1))) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, where m = len(queries).
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_2 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    r.val.length = m := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), r.val.length = m) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, 0 <= r[i] <= S, where S = sum_{j=0}^{n-1} nums[j].
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_3 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, i < m → ∃ v, Answer r i v ∧ 0 ≤ v ∧ v ≤ sliceSum nums := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, i < m → ∃ v, Answer r i v ∧ 0 ≤ v ∧ v ≤ sliceSum nums) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_4 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 1 <= i < m, r[i] <= r[i-1].
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_5 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, 1 ≤ i → i < m → ∀ a b, Answer r i a → Answer r (i - 1) b → a ≤ b := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, 1 ≤ i → i < m → ∀ a b, Answer r i a → Answer r (i - 1) b → a ≤ b) := by
  sorry

/-- Let M_i be the set of marked indices after the i-th query under the process where M_{-1} = empty set, and for each query first queries[i][0] is marked, then min(queries[i][1], number of remaining unmarked indices) unmarked indices with smallest pairs (nums[j], j) are marked. Whenever the function returns a result r, for every i with 0 <= i < m, r[i] = 0 if and only if M_i = { j | 0 <= j < n }.
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_6 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, i < m →
      (Answer r i 0 ↔ markedAfter nums queries (i + 1) = Finset.range nums.val.length) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, i < m →
      (Answer r i 0 ↔ markedAfter nums queries (i + 1) = Finset.range nums.val.length)) := by
  sorry

/-- Let M_i be the marked set after i queries under the process where M_{-1} = empty set and each query marks its own index and then the smallest remaining unmarked elements by the order (nums[j], j). For each i, let A_i = M_{i-1} union {queries[i][0]}. Whenever the function returns a result r, for every i with 0 <= i < m, r[i] = 0 if and only if queries[i][1] >= n - |A_i|.
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_7 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, i < m →
      (Answer r i 0 ↔ (n : Int) - ((markedWithOwn nums queries i).card : Int) ≤ queryK queries i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, i < m →
      (Answer r i 0 ↔ (n : Int) - ((markedWithOwn nums queries i).card : Int) ≤ queryK queries i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, r[i] = S - sum_{j in I_i} nums[j], where S = sum_{j=0}^{n-1} nums[j] and I_i = { queries[t][0] | 0 <= t <= i } with duplicates removed.
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, 0 <= queries[i][1] <= n - 1, and queries[i][1] = 0. -/
theorem spec_8 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (hk0 : ∀ i, i < m → queryK queries i = 0)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, i < m → Answer r i (sliceSum nums - sumOver nums (queryIdxSet queries i)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (hk0 : ∀ i, i < m → queryK queries i = 0)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, i < m → Answer r i (sliceSum nums - sumOver nums (queryIdxSet queries i))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 1 <= i < m, if queries[i][1] = 0 and there exists t with 0 <= t < i and queries[t][0] = queries[i][0], then r[i] = r[i-1].
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_9 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, 1 ≤ i → i < m → queryK queries i = 0 →
      (∃ t, t < i ∧ queryIdx queries t = queryIdx queries i) →
      ∃ v, Answer r i v ∧ Answer r (i - 1) v := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, 1 ≤ i → i < m → queryK queries i = 0 →
      (∃ t, t < i ∧ queryIdx queries t = queryIdx queries i) →
      ∃ v, Answer r i v ∧ Answer r (i - 1) v) := by
  sorry

/-- Let M_i be the marked set after i queries under the process where M_{-1} = empty set and each query marks its own index and then the smallest remaining unmarked elements by the order (nums[j], j). Whenever the function returns a result r, for every i with 1 <= i < m, if queries[i][1] = 0 and queries[i][0] not in M_{i-1}, then r[i] = r[i-1] - nums[queries[i][0]].
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_10 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, 1 ≤ i → i < m → queryK queries i = 0 →
      queryIdx queries i ∉ markedAfter nums queries i →
      ∃ a b, Answer r i a ∧ Answer r (i - 1) b ∧ a = b - numAt nums (queryIdx queries i) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, 1 ≤ i → i < m → queryK queries i = 0 →
      queryIdx queries i ∉ markedAfter nums queries i →
      ∃ a b, Answer r i a ∧ Answer r (i - 1) b ∧ a = b - numAt nums (queryIdx queries i)) := by
  sorry

/-- Let M_i be the marked set after i queries under the process where M_{-1} = empty set and each query marks its own index and then the smallest remaining unmarked elements by the order (nums[j], j). Whenever the function returns a result r, for every i with 1 <= i < m, r[i-1] - r[i] = sum over j with 0 <= j < n and j in M_i minus M_{i-1} of nums[j].
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1. -/
theorem spec_11 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, 1 ≤ i → i < m →
      ∃ a b, Answer r i a ∧ Answer r (i - 1) b ∧
        b - a = sumOver nums (markedAfter nums queries (i + 1) \ markedAfter nums queries i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, 1 ≤ i → i < m →
      ∃ a b, Answer r i a ∧ Answer r (i - 1) b ∧
        b - a = sumOver nums (markedAfter nums queries (i + 1) \ markedAfter nums queries i)) := by
  sorry

/-- Let M_i be the marked set after i queries under the process where M_{-1} = empty set and each query marks its own index and then the smallest remaining unmarked elements by the order (nums[j], j). Whenever the function returns a result r, for every i with 0 <= i < m, r[i] = c * (n - |M_i|).
  Preconditions: n = len(nums), m = len(queries), 1 <= n, 1 <= m <= n, n <= 100000, for every j with 0 <= j < n: 1 <= nums[j] <= 100000, for every i with 0 <= i < m: len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] <= n - 1, and there exists c such that for every j with 0 <= j < n, nums[j] = c. -/
theorem spec_12 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat) (c : Int)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (hc : ∀ j, j < n → numAt nums j = c)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r) :
    ∀ i, i < m → Answer r i (c * ((n : Int) - ((markedAfter nums queries (i + 1)).card : Int))) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (n m : Nat) (c : Int)
    (hn : n = nums.val.length) (hm : m = queries.val.length)
    (hn_pos : 1 ≤ n) (hm_pos : 1 ≤ m) (hm_le_n : m ≤ n) (hn_bound : n ≤ 100000)
    (hnums : ∀ j, j < n → 1 ≤ numAt nums j ∧ numAt nums j ≤ 100000)
    (hqlen : ∀ i, i < m → queryLen queries i = 2)
    (hidx : ∀ i, i < m → 0 ≤ queryFieldInt queries i 0 ∧ queryFieldInt queries i 0 < (n : Int))
    (hk : ∀ i, i < m → 0 ≤ queryK queries i ∧ queryK queries i ≤ (n : Int) - 1)
    (hc : ∀ j, j < n → numAt nums j = c)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.UnmarkedSumArray.unmarked_sum_array nums queries = ok r), ∀ i, i < m → Answer r i (c * ((n : Int) - ((markedAfter nums queries (i + 1)).card : Int)))) := by
  sorry

end AegisSpec.UnmarkedSumArray
