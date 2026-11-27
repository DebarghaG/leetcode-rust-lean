import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-binary-array-elements-equal-to-one-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinOperations

  namespace AegisSpec.MinOperations

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  @[simp] theorem vals_length (nums : Slice Std.I64) : (vals nums).length = nums.val.length := by
    simp [vals]

  theorem len_val (nums : Slice Std.I64) : (Slice.len nums).val = (vals nums).length := by
    simp [vals, Slice.len]

  abbrev OpSeq : Type := List ℕ

  abbrev covers (s j : ℕ) : Prop := s ≤ j ∧ j ≤ s + 2

  def coverCount (σ : OpSeq) (j : ℕ) : ℕ := σ.countP (fun s => decide (covers s j))

  def occCount (σ : OpSeq) (a : ℕ) : ℕ := σ.countP (fun s => decide (s = a))

  def EvenInt (a : ℤ) : Prop := ∃ t : ℤ, a = 2 * t

  def Cong2 (c : ℕ) (v : ℤ) : Prop := EvenInt ((c : ℤ) - (1 - v))

  def ValidOps (n : ℕ) (σ : OpSeq) : Prop := ∀ s ∈ σ, s ≤ n - 3

  def MakesAllOne (l : List ℤ) (σ : OpSeq) : Prop :=
    ∀ (j : ℕ) (v : ℤ), l[j]? = some v → Cong2 (coverCount σ j) v

  def Solvable (n : ℕ) (l : List ℤ) : Prop := ∃ σ : OpSeq, ValidOps n σ ∧ MakesAllOne l σ

  def IsMinLength (n : ℕ) (l : List ℤ) (r : ℤ) : Prop :=
    ∃ σ : OpSeq, ValidOps n σ ∧ MakesAllOne l σ ∧ (σ.length : ℤ) = r ∧
      ∀ τ : OpSeq, ValidOps n τ → MakesAllOne l τ → r ≤ (τ.length : ℤ)

  /-- Whenever the function returns a result r, the following holds. An operation sequence is a finite ordered list σ = (s_0, ..., s_{k-1}) with k ≥ 0 and 0 ≤ s_t ≤ n-3 for every t < k; its length is k. For 0 ≤ j < n, let c_j(σ) be the number of t < k with s_t ≤ j ≤ s_t+2. Say σ makes all elements 1 if for every j with 0 ≤ j < n, c_j(σ) mod 2 = 1 - nums[j]. Then: (a) if some operation sequence makes all elements 1, r is the least length of any such operation sequence (so r ≥ 0); (b) if no operation sequence makes all elements 1, r = -1.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) :
      (Solvable n (vals nums) → IsMinLength n (vals nums) r.val) ∧
        (¬ Solvable n (vals nums) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r), (Solvable n (vals nums) → IsMinLength n (vals nums) r.val) ∧
          (¬ Solvable n (vals nums) → r.val = -1)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic occurs) on any input satisfying the preconditions.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1) :
      ∃ r : Std.I64, min_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1), ∃ r : Std.I64, min_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, there exists an operation sequence σ = (s_0, ..., s_{r-1}) of length r (so 0 ≤ s_t ≤ n-3 for all t < r) such that for every j with 0 ≤ j < n, the number of t < r with s_t ≤ j ≤ s_t+2 is congruent to 1 - nums[j] modulo 2. In words, some sequence of r operations makes every element equal to 1.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      ∃ σ : OpSeq, (σ.length : ℤ) = r.val ∧ ValidOps n σ ∧ MakesAllOne (vals nums) σ := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), ∃ σ : OpSeq, (σ.length : ℤ) = r.val ∧ ValidOps n σ ∧ MakesAllOne (vals nums) σ) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, no operation sequence of length less than r makes all elements 1. Here an operation sequence of length k is a list σ=(s_0,...,s_{k-1}) with 0≤s_t≤n-3; it makes all elements 1 if for every j∈[0,n), #{t<k : s_t≤j≤s_t+2} ≡ 1-nums[j] (mod 2).
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      ∀ σ : OpSeq, ValidOps n σ → MakesAllOne (vals nums) σ → r.val ≤ (σ.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), ∀ σ : OpSeq, ValidOps n σ → MakesAllOne (vals nums) σ → r.val ≤ (σ.length : ℤ)) := by
    sorry

  /-- Whenever the function returns r = -1, no operation sequence of any finite length makes all elements 1. (An operation sequence of length k is a list σ=(s_0,...,s_{k-1}) with 0≤s_t≤n-3; it makes all elements 1 if for every j∈[0,n), #{t<k : s_t≤j≤s_t+2} ≡ 1-nums[j] (mod 2).)
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hminus : r.val = -1) :
      ¬ Solvable n (vals nums) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hminus : r.val = -1), ¬ Solvable n (vals nums)) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, 0 ≤ r ≤ n - 2.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_6 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), 0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 2) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if nums[i] = 1 for every i with 0 ≤ i < n.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_7 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) :
      (r.val = 0 ↔ ∀ x ∈ vals nums, x = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r), (r.val = 0 ↔ ∀ x ∈ vals nums, x = 1)) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, r ≡ n - (sum_{i=0}^{n-1} nums[i]) (mod 2).
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_8 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      EvenInt (r.val - ((n : ℤ) - (vals nums).sum)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), EvenInt (r.val - ((n : ℤ) - (vals nums).sum))) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, there exists a set A ⊆ {0,1,...,n-3} with |A| = r such that for every ordered list σ = (s_0, ..., s_{r-1}) with each s_t ∈ {0,1,...,n-3}, σ makes all elements 1 if and only if σ contains every element of A exactly once and contains no element outside A. Here σ makes all elements 1 means that for every j with 0 ≤ j < n, the number of t < r with s_t ≤ j ≤ s_t+2 is congruent to 1 - nums[j] modulo 2.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_9 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      ∃ A : Finset ℕ,
        (∀ a ∈ A, a ≤ n - 3) ∧ (A.card : ℤ) = r.val ∧
          ∀ σ : OpSeq, (σ.length : ℤ) = r.val → (∀ s ∈ σ, s ≤ n - 3) →
            (MakesAllOne (vals nums) σ ↔
              (∀ a ∈ A, occCount σ a = 1) ∧ (∀ s ∈ σ, s ∈ A)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), ∃ A : Finset ℕ,
          (∀ a ∈ A, a ≤ n - 3) ∧ (A.card : ℤ) = r.val ∧
            ∀ σ : OpSeq, (σ.length : ℤ) = r.val → (∀ s ∈ σ, s ≤ n - 3) →
              (MakesAllOne (vals nums) σ ↔
                (∀ a ∈ A, occCount σ a = 1) ∧ (∀ s ∈ σ, s ∈ A))) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, for every operation sequence σ=(s_0,...,s_{r-1}) of length r that makes all elements 1, the number of t<r with s_t = n-3 is congruent to 1 - nums[n-1] modulo 2. (An operation sequence makes all elements 1 if for every j∈[0,n), #{t : s_t≤j≤s_t+2} ≡ 1-nums[j] (mod 2).)
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_10 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      ∀ σ : OpSeq, (σ.length : ℤ) = r.val → ValidOps n σ → MakesAllOne (vals nums) σ →
        ∀ v : ℤ, (vals nums)[n - 1]? = some v → Cong2 (occCount σ (n - 3)) v := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), ∀ σ : OpSeq, (σ.length : ℤ) = r.val → ValidOps n σ → MakesAllOne (vals nums) σ →
          ∀ v : ℤ, (vals nums)[n - 1]? = some v → Cong2 (occCount σ (n - 3)) v) := by
    sorry

  /-- Whenever the function returns a result r with r ≠ -1, for every operation sequence σ=(s_0,...,s_{r-1}) of length r that makes all elements 1, the number of t<r with s_t = 0 is congruent to 1 - nums[0] modulo 2. (An operation sequence makes all elements 1 if for every j∈[0,n), #{t : s_t≤j≤s_t+2} ≡ 1-nums[j] (mod 2).)
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_11 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1) :
      ∀ σ : OpSeq, (σ.length : ℤ) = r.val → ValidOps n σ → MakesAllOne (vals nums) σ →
        ∀ v : ℤ, (vals nums)[0]? = some v → Cong2 (occCount σ 0) v := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r) (hne : r.val ≠ -1), ∀ σ : OpSeq, (σ.length : ℤ) = r.val → ValidOps n σ → MakesAllOne (vals nums) σ →
          ∀ v : ℤ, (vals nums)[0]? = some v → Cong2 (occCount σ 0) v) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists an index s with 0 ≤ s ≤ n-3 such that nums[s]=nums[s+1]=nums[s+2]=0 and nums[j]=1 for every j with 0 ≤ j < n and j ∉ {s,s+1,s+2}.
    Preconditions: Let n = len(nums). The input satisfies 3 ≤ n ≤ 100000 and, for every i with 0 ≤ i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_12 (nums : Slice Std.I64) (n : ℕ)
      (hn : n = (vals nums).length)
      (hlo : 3 ≤ n) (hhi : n ≤ 100000)
      (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
      (r : Std.I64) (hret : min_operations nums = ok r) :
      (r.val = 1 ↔ ∃ s : ℕ, s ≤ n - 3 ∧
        (∀ j : ℕ, covers s j → ∀ v : ℤ, (vals nums)[j]? = some v → v = 0) ∧
          ∀ (j : ℕ) (v : ℤ), (vals nums)[j]? = some v → ¬ covers s j → v = 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hn : n = (vals nums).length)
        (hlo : 3 ≤ n) (hhi : n ≤ 100000)
        (hbin : ∀ (i : ℕ) (v : ℤ), (vals nums)[i]? = some v → v = 0 ∨ v = 1)
        (r : Std.I64) (hret : min_operations nums = ok r), (r.val = 1 ↔ ∃ s : ℕ, s ≤ n - 3 ∧
          (∀ j : ℕ, covers s j → ∀ v : ℤ, (vals nums)[j]? = some v → v = 0) ∧
            ∀ (j : ℕ) (v : ℤ), (vals nums)[j]? = some v → ¬ covers s j → v = 1)) := by
    sorry

  end AegisSpec.MinOperations
