import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-exceed-threshold-value-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def entry (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) : ℤ :=
    (nums.val.get ⟨i, h⟩).val

  def msetOf (nums : Slice Std.I64) : Multiset ℤ := (vals nums : Multiset ℤ)

  def below (nums : Slice Std.I64) (k : ℤ) : Multiset ℤ :=
    ((vals nums).filter (fun v => decide (v < k)) : Multiset ℤ)

  def countLt (nums : Slice Std.I64) (k : ℤ) : ℕ := (below nums k).card

  def Step (s t : Multiset ℤ) : Prop :=
    ∃ (a b : ℤ) (rest : Multiset ℤ),
      a ≤ b ∧ (∀ x ∈ rest, b ≤ x) ∧ s = rest + {a, b} ∧ t = rest + {2 * a + b}

  def Reach : ℕ → Multiset ℤ → Multiset ℤ → Prop
    | 0, s, t => s = t
    | n + 1, s, t => ∃ u, Step s u ∧ Reach n u t

  def AllGe (k : ℤ) (s : Multiset ℤ) : Prop := ∀ x ∈ s, k ≤ x

  def AnswerExists (nums : Slice Std.I64) (k : ℤ) : Prop :=
    ∃ n t, Reach n (msetOf nums) t ∧ AllGe k t

  def Solvable (nums : Slice Std.I64) (k : ℤ) (n : ℕ) : Prop :=
    ∃ t, Reach n (msetOf nums) t ∧ AllGe k t

  def IsMinOps (nums : Slice Std.I64) (k : ℤ) (n : ℕ) : Prop :=
    Solvable nums k n ∧ ∀ j, j < n → ¬ Solvable nums k j

  /-- The function returns a result r and does not fail. The value r is the least integer t >= 0 such that some sequence of t operations applied to the initial multiset of nums yields a multiset in which every element is >= k. Equivalently, after r operations every element is >= k, and for every integer t with 0 <= t < r, no sequence of t operations yields a multiset in which every element is >= k.
    Preconditions: 2 <= len(nums) <= 2 * 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists: there is a finite sequence of operations from the multiset of nums to a multiset all of whose elements are >= k. An operation on a multiset with at least two elements replaces one occurrence of its smallest element a and one occurrence of its second smallest element b, with a <= b, by 2*a + b. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 5)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧ 0 ≤ r.val ∧
        IsMinOps nums k.val r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 5)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧ 0 ≤ r.val ∧
          IsMinOps nums k.val r.val.toNat) := by
    sorry

  /-- The function returns a result r and does not panic, overflow, or fail.
    Preconditions: 2 <= len(nums) <= 2 * 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists: there is a finite sequence of operations from the multiset of nums to a multiset all of whose elements are >= k. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 5)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 5)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 2*r >= c.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. Let c be the number of indices i with 0 <= i < len(nums) and nums[i] < k. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        2 * r.val ≥ (countLt nums k.val : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          2 * r.val ≥ (countLt nums k.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= c.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. Let c be the number of indices i with 0 <= i < len(nums) and nums[i] < k. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        r.val ≤ (countLt nums k.val : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          r.val ≤ (countLt nums k.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums) - 1.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        r.val ≤ (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          r.val ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] >= k.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        (r.val = 0 ↔ ∀ i (h : i < nums.val.length), k.val ≤ entry nums i h) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          (r.val = 0 ↔ ∀ i (h : i < nums.val.length), k.val ≤ entry nums i h)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists; exactly one index i has nums[i] < k. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val)
      (hcount : countLt nums k.val = 1) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r → r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val)
        (hcount : countLt nums k.val = 1), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if nums[0] >= k and nums[1] >= k then r = 0; otherwise r = 1.
    Preconditions: len(nums) = 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : nums.val.length = 2)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ((k.val ≤ entry nums 0 (by omega) ∧ k.val ≤ entry nums 1 (by omega)) → r.val = 0) ∧
        ((¬ (k.val ≤ entry nums 0 (by omega) ∧ k.val ≤ entry nums 1 (by omega))) →
          r.val = 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : nums.val.length = 2)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ((k.val ≤ entry nums 0 (by omega) ∧ k.val ≤ entry nums 1 (by omega)) → r.val = 0) ∧
          ((¬ (k.val ≤ entry nums 0 (by omega) ∧ k.val ≤ entry nums 1 (by omega))) →
            r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, if 2*a + b >= k then r = 1, and otherwise r = 2.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists; exactly two indices i have nums[i] < k. Let a and b be those two values with a <= b. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val)
      (hcount : countLt nums k.val = 2) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ∀ a b : ℤ, a ≤ b → below nums k.val = {a, b} →
          ((k.val ≤ 2 * a + b → r.val = 1) ∧ (2 * a + b < k.val → r.val = 2)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val)
        (hcount : countLt nums k.val = 2), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ∀ a b : ℤ, a ≤ b → below nums k.val = {a, b} →
            ((k.val ≤ 2 * a + b → r.val = 1) ∧ (2 * a + b < k.val → r.val = 2))) := by
    sorry

  /-- Whenever the function returns a result r, there exists a sequence of exactly r operations from the initial multiset of nums that yields a multiset in which every element is >= k.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        Solvable nums k.val r.val.toNat := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          Solvable nums k.val r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every integer t with 0 <= t < r, no sequence of t operations from the initial multiset of nums yields a multiset in which every element is >= k.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val) :
      ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
        ∀ t : ℤ, 0 ≤ t → t < r.val → ¬ Solvable nums k.val t.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val), ∀ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r →
          ∀ t : ℤ, 0 ≤ t → t < r.val → ¬ Solvable nums k.val t.toNat) := by
    sorry

  /-- Whenever min_operations(nums, k) returns r and min_operations(nums', k) returns r', we have r = r'.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; the answer exists. Let nums' be any permutation of nums, also satisfying the same constraints and answer-existence promise. -/
  theorem spec_12 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val)
      (hperm : nums'.val.Perm nums.val)
      (hbnd' : ∀ i (h : i < nums'.val.length), 1 ≤ entry nums' i h ∧ entry nums' i h ≤ 10 ^ 9)
      (hex' : AnswerExists nums' k.val) :
      ∀ (r r' : Std.I64), Aegis.MinOperations.min_operations nums k = ok r →
        Aegis.MinOperations.min_operations nums' k = ok r' → r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val)
        (hperm : nums'.val.Perm nums.val)
        (hbnd' : ∀ i (h : i < nums'.val.length), 1 ≤ entry nums' i h ∧ entry nums' i h ≤ 10 ^ 9)
        (hex' : AnswerExists nums' k.val), ∀ (r r' : Std.I64), Aegis.MinOperations.min_operations nums k = ok r →
          Aegis.MinOperations.min_operations nums' k = ok r' → r = r') := by
    sorry

  /-- Whenever min_operations(nums, k1) returns r1 and min_operations(nums, k2) returns r2, we have r1 <= r2.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k1 <= k2 <= 10^9; both inputs (nums, k1) and (nums, k2) have an answer. -/
  theorem spec_13 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ 10 ^ 9)
      (hans1 : AnswerExists nums k1.val)
      (hans2 : AnswerExists nums k2.val) :
      ∀ r1 r2 : Std.I64, Aegis.MinOperations.min_operations nums k1 = ok r1 →
        Aegis.MinOperations.min_operations nums k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ 10 ^ 9)
        (hans1 : AnswerExists nums k1.val)
        (hans2 : AnswerExists nums k2.val), ∀ r1 r2 : Std.I64, Aegis.MinOperations.min_operations nums k1 = ok r1 →
          Aegis.MinOperations.min_operations nums k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever min_operations(nums, k) returns r and min_operations(nums', k) returns r', we have r' <= r.
    Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9; both (nums, k) and (nums', k) have an answer; nums' has the same length as nums and for every i, nums[i] <= nums'[i] <= 10^9. -/
  theorem spec_14 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen : 2 ≤ nums.val.length)
      (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hex : AnswerExists nums k.val)
      (hlen' : nums'.val.length = nums.val.length)
      (hpoint : ∀ i (h : i < nums.val.length),
        entry nums i h ≤ entry nums' i (by omega) ∧ entry nums' i (by omega) ≤ 10 ^ 9)
      (hex' : AnswerExists nums' k.val) :
      ∀ (r r' : Std.I64), Aegis.MinOperations.min_operations nums k = ok r →
        Aegis.MinOperations.min_operations nums' k = ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen : 2 ≤ nums.val.length)
        (hbnd : ∀ i (h : i < nums.val.length), 1 ≤ entry nums i h ∧ entry nums i h ≤ 10 ^ 9)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hex : AnswerExists nums k.val)
        (hlen' : nums'.val.length = nums.val.length)
        (hpoint : ∀ i (h : i < nums.val.length),
          entry nums i h ≤ entry nums' i (by omega) ∧ entry nums' i (by omega) ≤ 10 ^ 9)
        (hex' : AnswerExists nums' k.val), ∀ (r r' : Std.I64), Aegis.MinOperations.min_operations nums k = ok r →
          Aegis.MinOperations.min_operations nums' k = ok r' → r'.val ≤ r.val) := by
    sorry

  end AegisSpec.MinOperations
