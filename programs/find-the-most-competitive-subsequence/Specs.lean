import Aegis.MostCompetitive.Code.Funs

/-!
# Specifications of `Aegis.MostCompetitive.most_competitive`

LeetCode problem `find-the-most-competitive-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MostCompetitive

def Subseq (r s : List Std.I64) : Prop :=
  ∃ idx : Fin r.length → Fin s.length,
    (∀ i j : Fin r.length, i < j → idx i < idx j) ∧
      ∀ i : Fin r.length, r.get i = s.get (idx i)

def LexLt (r s : List Std.I64) : Prop :=
  ∃ (p : Nat) (a b : Std.I64),
    r[p]? = some a ∧ s[p]? = some b ∧ a.val < b.val ∧ ∀ q : Nat, q < p → r[q]? = s[q]?

def LexLe (r s : List Std.I64) : Prop :=
  r = s ∨ LexLt r s

def IsMinOn (xs : List Std.I64) (lo hi : Nat) (v : Std.I64) : Prop :=
  (∀ (i : Nat) (x : Std.I64), lo ≤ i → i ≤ hi → xs[i]? = some x → v.val ≤ x.val) ∧
    ∃ i : Nat, lo ≤ i ∧ i ≤ hi ∧ xs[i]? = some v

def Nondecreasing (xs : List Std.I64) : Prop :=
  ∀ (i j : Nat) (a b : Std.I64), i < j → xs[i]? = some a → xs[j]? = some b → a.val ≤ b.val

def Nonincreasing (xs : List Std.I64) : Prop :=
  ∀ (i j : Nat) (a b : Std.I64), i < j → xs[i]? = some a → xs[j]? = some b → b.val ≤ a.val

/-- The function returns a result r (a Vec of i64) such that: (a) len(r) = k; (b) there exist indices i_0 < i_1 < ... < i_{k-1} in [0, len(nums)-1] with r[j] = nums[i_j] for all 0 <= j < k; (c) for every subsequence s of nums of length k, r is lexicographically less than or equal to s, where lexicographic comparison means r = s or there exists an index p with 0 <= p < k such that r[p] < s[p] and for all q < p, r[q] = s[q].
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        Subseq r.val nums.val ∧
        (∀ s : List Std.I64, Subseq s nums.val → (s.length : Int) = k.val → LexLe r.val s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        Subseq r.val nums.val ∧
        (∀ s : List Std.I64, Subseq s nums.val → (s.length : Int) = k.val → LexLe r.val s)) := by
  sorry

/-- The function returns a result r with len(r) = k.
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧ (r.val.length : Int) = k.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧ (r.val.length : Int) = k.val) := by
  sorry

/-- The function returns a result r such that len(r) = k and there exist indices i_0 < i_1 < ... < i_{k-1} in [0, len(nums)-1] with r[j] = nums[i_j] for all 0 <= j < k.
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧ Subseq r.val nums.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧ Subseq r.val nums.val) := by
  sorry

/-- The function returns a result r such that len(r) = k and for every subsequence s of nums of length k, r is lexicographically less than or equal to s (i.e., r = s or there exists an index p with 0 <= p < k such that r[p] < s[p] and for all q < p, r[q] = s[q]).
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ s : List Std.I64, Subseq s nums.val → (s.length : Int) = k.val → LexLe r.val s) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ s : List Std.I64, Subseq s nums.val → (s.length : Int) = k.val → LexLe r.val s)) := by
  sorry

/-- The function returns a result r such that for every j with 0 <= j < len(r), 0 <= r[j] <= 10^9.
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        ∀ (j : Nat) (h : j < r.val.length),
          0 ≤ (r.val.get ⟨j, h⟩).val ∧ (r.val.get ⟨j, h⟩).val ≤ 1000000000 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        ∀ (j : Nat) (h : j < r.val.length),
          0 ≤ (r.val.get ⟨j, h⟩).val ∧ (r.val.get ⟨j, h⟩).val ≤ 1000000000) := by
  sorry

/-- The function returns a result r with len(r) = 1 and r[0] = min{ nums[i] : 0 <= i < len(nums) }. Equivalently, r[0] <= nums[i] for all 0 <= i < len(nums), and there exists an index i with r[0] = nums[i].
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, 1 <= k <= len(nums), and k = 1. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) (hk_one : k.val = 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = 1 ∧
        (∀ a : Std.I64, r[0]? = some a → IsMinOn nums.val 0 (nums.val.length - 1) a) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) (hk_one : k.val = 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = 1 ∧
        (∀ a : Std.I64, r[0]? = some a → IsMinOn nums.val 0 (nums.val.length - 1) a)) := by
  sorry

/-- The function returns a result r with len(r) = len(nums) and for every i with 0 <= i < len(nums), r[i] = nums[i].
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, 1 <= k <= len(nums), and k = len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hk_len : k.val = (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = (nums.val.length : Int) ∧
        (∀ (i : Nat) (h : i < nums.val.length), r.val[i]? = some (nums.val.get ⟨i, h⟩)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hk_len : k.val = (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = (nums.val.length : Int) ∧
        (∀ (i : Nat) (h : i < nums.val.length), r.val[i]? = some (nums.val.get ⟨i, h⟩))) := by
  sorry

/-- The function returns a result r with len(r) = k and for every j with 0 <= j < k, r[j] = v.
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, 1 <= k <= len(nums), and there exists a value v such that for all i with 0 <= i < len(nums), nums[i] = v. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (v : Int)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hconst : ∀ (i : Nat) (h : i < nums.val.length), (nums.val.get ⟨i, h⟩).val = v) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ (j : Nat) (h : j < r.val.length), (r.val.get ⟨j, h⟩).val = v) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (v : Int)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hconst : ∀ (i : Nat) (h : i < nums.val.length), (nums.val.get ⟨i, h⟩).val = v), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ (j : Nat) (h : j < r.val.length), (r.val.get ⟨j, h⟩).val = v)) := by
  sorry

/-- The function returns a result r such that len(r) = k and r[0] = min{ nums[i] : 0 <= i <= len(nums) - k }.
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ a : Std.I64,
          r[0]? = some a → IsMinOn nums.val 0 (nums.val.length - k.val.toNat) a) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ a : Std.I64,
          r[0]? = some a → IsMinOn nums.val 0 (nums.val.length - k.val.toNat) a)) := by
  sorry

/-- For every nums and k satisfying the preconditions, the function returns a result (i.e., it does not panic, overflow, or go out of bounds).
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.MostCompetitive.most_competitive nums k = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64, Aegis.MostCompetitive.most_competitive nums k = ok r) := by
  sorry

/-- The function returns a result r such that len(r) = k and for every subsequence s of nums of length k, if s != r then r is lexicographically strictly less than s (i.e., there exists an index p with 0 <= p < k such that r[p] < s[p] and for all q < p, r[q] = s[q]).
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, and 1 <= k <= len(nums). -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ s : List Std.I64,
          Subseq s nums.val → (s.length : Int) = k.val → s ≠ r.val → LexLt r.val s) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ s : List Std.I64,
          Subseq s nums.val → (s.length : Int) = k.val → s ≠ r.val → LexLt r.val s)) := by
  sorry

/-- The function returns a result r with len(r) = k and for every j with 0 <= j < k, r[j] = nums[j].
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, 1 <= k <= len(nums), and nums is non-decreasing (for all i < j with 0 <= i < j < len(nums), nums[i] <= nums[j]). -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hmono : Nondecreasing nums.val) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ j : Nat, j < k.val.toNat → r.val[j]? = nums.val[j]?) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hmono : Nondecreasing nums.val), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ j : Nat, j < k.val.toNat → r.val[j]? = nums.val[j]?)) := by
  sorry

/-- The function returns a result r with len(r) = k and for every j with 0 <= j < k, r[j] = nums[len(nums) - k + j].
  Preconditions: 1 <= len(nums) <= 10^5, for all i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9, 1 <= k <= len(nums), and nums is non-increasing (for all i < j with 0 <= i < j < len(nums), nums[i] >= nums[j]). -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hanti : Nonincreasing nums.val) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ j : Nat,
          j < k.val.toNat → r.val[j]? = nums.val[nums.val.length - k.val.toNat + j]?) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hanti : Nonincreasing nums.val), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MostCompetitive.most_competitive nums k = ok r ∧
        (r.val.length : Int) = k.val ∧
        (∀ j : Nat,
          j < k.val.toNat → r.val[j]? = nums.val[nums.val.length - k.val.toNat + j]?)) := by
  sorry

end AegisSpec.MostCompetitive
