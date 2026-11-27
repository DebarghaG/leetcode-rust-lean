import Aegis.TriangularSum.Code.Funs

/-!
# Specifications of `Aegis.TriangularSum.triangular_sum`

LeetCode problem `find-triangular-sum-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.TriangularSum

  namespace AegisSpec.TriangularSum

  def vals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

  def Digits (l : List ℤ) : Prop :=
    ∀ (i : ℕ) (hi : i < l.length), 0 ≤ l.get ⟨i, hi⟩ ∧ l.get ⟨i, hi⟩ ≤ 9

  def weightedSum (l : List ℤ) : ℤ :=
    (Finset.range l.length).sum (fun i => (Nat.choose (l.length - 1) i : ℤ) * l.getD i 0)

  def swapAt (l : List ℤ) (i j : ℕ) : List ℤ := (l.set i (l.getD j 0)).set j (l.getD i 0)

  def adjacentSums (l : List ℤ) : List ℤ := (l.zip l.tail).map (fun p => (p.1 + p.2) % 10)

  /-- The function returns a result r and r = (Σ_{i=0}^{n-1} C(n-1, i) * nums[i]) mod 10, where C(a,b) denotes the binomial coefficient (a choose b) and mod 10 is the nonnegative remainder modulo 10.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, 0 <= nums[i] <= 9. -/
  theorem spec_1 (nums : Slice I64)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : Digits (vals nums)) :
      ∃ r, triangular_sum nums = ok r ∧ r.val = weightedSum (vals nums) % 10 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : Digits (vals nums)), ∃ r, triangular_sum nums = ok r ∧ r.val = weightedSum (vals nums) % 10) := by
    sorry

  /-- The function returns a result r and 0 <= r <= 9.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, 0 <= nums[i] <= 9. -/
  theorem spec_2 (nums : Slice I64)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : Digits (vals nums)) :
      ∃ r, triangular_sum nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 9 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : Digits (vals nums)), ∃ r, triangular_sum nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 9) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, 0 <= nums[i] <= 9. -/
  theorem spec_3 (nums : Slice I64)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : Digits (vals nums)) :
      ∃ r, triangular_sum nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : Digits (vals nums)), ∃ r, triangular_sum nums = ok r) := by
    sorry

  /-- The function returns a result r and r = nums[0].
    Preconditions: Let n = len(nums). n = 1. 0 <= nums[0] <= 9. -/
  theorem spec_4 (nums : Slice I64)
      (hn : (vals nums).length = 1)
      (hd0 : 0 ≤ (vals nums).getD 0 0) (hd9 : (vals nums).getD 0 0 ≤ 9) :
      ∃ r, triangular_sum nums = ok r ∧ r.val = (vals nums).getD 0 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hn : (vals nums).length = 1)
        (hd0 : 0 ≤ (vals nums).getD 0 0) (hd9 : (vals nums).getD 0 0 ≤ 9), ∃ r, triangular_sum nums = ok r ∧ r.val = (vals nums).getD 0 0) := by
    sorry

  /-- The function returns a result r and r = (nums[0] + nums[1]) mod 10.
    Preconditions: Let n = len(nums). n = 2. 0 <= nums[0] <= 9 and 0 <= nums[1] <= 9. -/
  theorem spec_5 (nums : Slice I64)
      (hn : (vals nums).length = 2)
      (hd0 : 0 ≤ (vals nums).getD 0 0) (hd0' : (vals nums).getD 0 0 ≤ 9)
      (hd1 : 0 ≤ (vals nums).getD 1 0) (hd1' : (vals nums).getD 1 0 ≤ 9) :
      ∃ r, triangular_sum nums = ok r ∧
        r.val = ((vals nums).getD 0 0 + (vals nums).getD 1 0) % 10 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hn : (vals nums).length = 2)
        (hd0 : 0 ≤ (vals nums).getD 0 0) (hd0' : (vals nums).getD 0 0 ≤ 9)
        (hd1 : 0 ≤ (vals nums).getD 1 0) (hd1' : (vals nums).getD 1 0 ≤ 9), ∃ r, triangular_sum nums = ok r ∧
          r.val = ((vals nums).getD 0 0 + (vals nums).getD 1 0) % 10) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, nums[i] = 0. -/
  theorem spec_6 (nums : Slice I64)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ = 0) :
      ∃ r, triangular_sum nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ = 0), ∃ r, triangular_sum nums = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = (d * 2^{n-1}) mod 10.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. There exists a digit d with 0 <= d <= 9 such that for every i with 0 <= i < n, nums[i] = d. -/
  theorem spec_7 (nums : Slice I64) (d : ℤ)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd0 : 0 ≤ d) (hd9 : d ≤ 9)
      (hconst : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ = d) :
      ∃ r, triangular_sum nums = ok r ∧ r.val = (d * 2 ^ ((vals nums).length - 1)) % 10 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (d : ℤ)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd0 : 0 ≤ d) (hd9 : d ≤ 9)
        (hconst : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ = d), ∃ r, triangular_sum nums = ok r ∧ r.val = (d * 2 ^ ((vals nums).length - 1)) % 10) := by
    sorry

  /-- Let r be the result of the function on nums and r' be the result of the function on nums'. Then r = r'.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every j with 0 <= j < n, 0 <= nums[j] <= 9. Let i be an index with 0 <= i < n. Define the array nums' of length n by nums'[i] = nums[n-1-i], nums'[n-1-i] = nums[i], and nums'[j] = nums[j] for all j not equal to i or n-1-i. (If i = n-1-i, then nums' = nums.) -/
  theorem spec_8 (nums nums' : Slice I64) (i : ℕ)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : Digits (vals nums))
      (hi : i < (vals nums).length)
      (hnums' : vals nums' = swapAt (vals nums) i ((vals nums).length - 1 - i))
      (r r' : I64) (hr : triangular_sum nums = ok r) (hr' : triangular_sum nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice I64) (i : ℕ)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : Digits (vals nums))
        (hi : i < (vals nums).length)
        (hnums' : vals nums' = swapAt (vals nums) i ((vals nums).length - 1 - i))
        (r r' : I64) (hr : triangular_sum nums = ok r) (hr' : triangular_sum nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let rC be the result of the function on C, rA be the result on A, and rB be the result on B. Then rC = (c * rA + d * rB) mod 10.
    Preconditions: Let n be an integer with 1 <= n <= 1000. Let A and B be arrays of length n with entries in 0..9. Let c and d be digits (0 <= c,d <= 9). Define the array C of length n by C[i] = (c * A[i] + d * B[i]) mod 10 for 0 <= i < n. Then C has entries in 0..9. -/
  theorem spec_9 (A B C : Slice I64) (c d : ℤ)
      (hn1 : 1 ≤ (vals A).length) (hn2 : (vals A).length ≤ 1000)
      (hB : (vals B).length = (vals A).length)
      (hC : (vals C).length = (vals A).length)
      (hAd : Digits (vals A)) (hBd : Digits (vals B))
      (hc0 : 0 ≤ c) (hc9 : c ≤ 9) (hd0 : 0 ≤ d) (hd9 : d ≤ 9)
      (hCdef : vals C = (vals A).zipWith (fun a b => (c * a + d * b) % 10) (vals B))
      (rC rA rB : I64)
      (hrC : triangular_sum C = ok rC) (hrA : triangular_sum A = ok rA)
      (hrB : triangular_sum B = ok rB) :
      rC.val = (c * rA.val + d * rB.val) % 10 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (A B C : Slice I64) (c d : ℤ)
        (hn1 : 1 ≤ (vals A).length) (hn2 : (vals A).length ≤ 1000)
        (hB : (vals B).length = (vals A).length)
        (hC : (vals C).length = (vals A).length)
        (hAd : Digits (vals A)) (hBd : Digits (vals B))
        (hc0 : 0 ≤ c) (hc9 : c ≤ 9) (hd0 : 0 ≤ d) (hd9 : d ≤ 9)
        (hCdef : vals C = (vals A).zipWith (fun a b => (c * a + d * b) % 10) (vals B))
        (rC rA rB : I64)
        (hrC : triangular_sum C = ok rC) (hrA : triangular_sum A = ok rA)
        (hrB : triangular_sum B = ok rB), rC.val = (c * rA.val + d * rB.val) % 10) := by
    sorry

  /-- The function returns a result r and r is even (i.e., r mod 2 = 0).
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, nums[i] is even (i.e., nums[i] ∈ {0,2,4,6,8}). -/
  theorem spec_10 (nums : Slice I64)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ % 2 = 0) :
      ∃ r, triangular_sum nums = ok r ∧ r.val % 2 = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ % 2 = 0), ∃ r, triangular_sum nums = ok r ∧ r.val % 2 = 0) := by
    sorry

  /-- The function returns a result r and r is a multiple of 5 (i.e., r ∈ {0,5}).
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, nums[i] is a multiple of 5 (i.e., nums[i] ∈ {0,5}). -/
  theorem spec_11 (nums : Slice I64)
      (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ % 5 = 0) :
      ∃ r, triangular_sum nums = ok r ∧ (r.val = 0 ∨ r.val = 5) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (hn1 : 1 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums).get ⟨i, hi⟩ % 5 = 0), ∃ r, triangular_sum nums = ok r ∧ (r.val = 0 ∨ r.val = 5)) := by
    sorry

  /-- Let m = n - 1 and define newNums of length m by newNums[i] = (nums[i] + nums[i+1]) mod 10 for 0 <= i < m. Then the function returns a result r and r is the result of the function on newNums.
    Preconditions: Let n = len(nums). 2 <= n <= 1000. For every i with 0 <= i < n, 0 <= nums[i] <= 9. -/
  theorem spec_12 (nums newNums : Slice I64)
      (hn1 : 2 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
      (hd : Digits (vals nums))
      (hnew : vals newNums = adjacentSums (vals nums)) :
      ∃ r, triangular_sum nums = ok r ∧
        ∃ r', triangular_sum newNums = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums newNums : Slice I64)
        (hn1 : 2 ≤ (vals nums).length) (hn2 : (vals nums).length ≤ 1000)
        (hd : Digits (vals nums))
        (hnew : vals newNums = adjacentSums (vals nums)), ∃ r, triangular_sum nums = ok r ∧
          ∃ r', triangular_sum newNums = ok r' ∧ r.val = r'.val) := by
    sorry

  end AegisSpec.TriangularSum
