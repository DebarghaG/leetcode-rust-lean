import Aegis.MaximumProduct.Code.Funs

/-!
# Specifications of `Aegis.MaximumProduct.maximum_product`

LeetCode problem `maximum-product-after-k-increments`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumProduct

open Aegis.MaximumProduct (maximum_product)

def M : ℤ := 1000000007

def nth (nums : Slice Std.I64) (i : ℕ) (hi : i < nums.val.length) : ℤ :=
  (nums.val.get ⟨i, hi⟩).val

def ValidNums (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    ∀ (i : ℕ) (hi : i < nums.val.length), 0 ≤ nth nums i hi ∧ nth nums i hi ≤ 1000000

def ValidK (k : Std.I64) : Prop := 1 ≤ k.val ∧ k.val ≤ 100000

def ValidNumsPos (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    ∀ (i : ℕ) (hi : i < nums.val.length), 1 ≤ nth nums i hi ∧ nth nums i hi ≤ 1000000

def FeasibleLE (n : ℕ) (k : ℤ) (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ (Finset.univ : Finset (Fin n)).sum d ≤ k

def FeasibleEq (n : ℕ) (k : ℤ) (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ (Finset.univ : Finset (Fin n)).sum d = k

def prodAlloc (nums : Slice Std.I64) (d : Fin nums.val.length → ℤ) : ℤ :=
  (Finset.univ : Finset (Fin nums.val.length)).prod (fun i => nth nums i.val i.isLt + d i)

def baseProd (nums : Slice Std.I64) : ℤ := prodAlloc nums (fun _ => 0)

def IsMaxLE (nums : Slice Std.I64) (k : ℤ) (P : ℤ) : Prop :=
  (∃ d : Fin nums.val.length → ℤ, FeasibleLE nums.val.length k d ∧ prodAlloc nums d = P) ∧
    ∀ d : Fin nums.val.length → ℤ, FeasibleLE nums.val.length k d → prodAlloc nums d ≤ P

def IsMaxEq (nums : Slice Std.I64) (k : ℤ) (P : ℤ) : Prop :=
  (∃ d : Fin nums.val.length → ℤ, FeasibleEq nums.val.length k d ∧ prodAlloc nums d = P) ∧
    ∀ d : Fin nums.val.length → ℤ, FeasibleEq nums.val.length k d → prodAlloc nums d ≤ P

def countZeros (nums : Slice Std.I64) : ℕ :=
  nums.val.countP (fun x => decide (x.val = 0))

def IsZeroReplaced (nums nums' : Slice Std.I64) : Prop :=
  nums'.val = nums.val.map (fun x => if x.val = 0 then 1#i64 else x)

def IsPermuted (nums nums' : Slice Std.I64) (σ : Equiv.Perm (Fin nums.val.length)) : Prop :=
  nums'.val = List.ofFn (fun i => nums.val.get (σ i))

/-- Let P* be the maximum, over all integer vectors (d_0,...,d_{n-1}) with d_i >= 0 for every i and sum_{i=0}^{n-1} d_i <= k, of the ordinary integer product product_{i=0}^{n-1} (nums[i] + d_i). Under the preconditions, the call maximum_product(nums,k) returns a result r and r is the least nonnegative residue of P* modulo M: 0 <= r < M and r is congruent to P* modulo M. The maximum is taken before the modulo operation.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) :
    ∃ P : ℤ, IsMaxLE nums k.val P ∧
      ∃ r : Std.I64, maximum_product nums k = ok r ∧
        0 ≤ r.val ∧ r.val < M ∧ r.val ≡ P [ZMOD M] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k), ∃ P : ℤ, IsMaxLE nums k.val P ∧
      ∃ r : Std.I64, maximum_product nums k = ok r ∧
        0 ≤ r.val ∧ r.val < M ∧ r.val ≡ P [ZMOD M]) := by
  sorry

/-- For every input satisfying the preconditions, the call maximum_product(nums,k) returns a value of the form Result.ok r; it does not fail. In particular, no panic, out-of-bounds access, or 64-bit arithmetic overflow occurs in the computation.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) :
    ∃ r : Std.I64, maximum_product nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k), ∃ r : Std.I64, maximum_product nums k = ok r) := by
  sorry

/-- If len(nums) = 1, then whenever maximum_product(nums,k) returns r, r = (nums[0] + k) mod M, where the residue is the least nonnegative one.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) (h1 : nums.val.length = 1) :
    ∀ r : Std.I64, maximum_product nums k = ok r →
      r.val = (nth nums 0 (by omega) + k.val) % M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) (h1 : nums.val.length = 1), ∀ r : Std.I64, maximum_product nums k = ok r →
      r.val = (nth nums 0 (by omega) + k.val) % M) := by
  sorry

/-- Let z = number of indices i with 0 <= i < len(nums) such that nums[i] = 0. If z > k, then whenever maximum_product(nums,k) returns r, r = 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (hz : (countZeros nums : ℤ) > k.val) :
    ∀ r : Std.I64, maximum_product nums k = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (hz : (countZeros nums : ℤ) > k.val), ∀ r : Std.I64, maximum_product nums k = ok r → r.val = 0) := by
  sorry

/-- Suppose nums[i] = c for every i with 0 <= i < n = len(nums). Let q = k / n using integer division and s = k mod n. Then whenever maximum_product(nums,k) returns r, r = ((c + q + 1)^s * (c + q)^(n-s)) mod M. The exponentiation and multiplication on the left are the ordinary integer product before the final least nonnegative residue modulo M.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (c : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (hunif : ∀ (i : ℕ) (hi : i < nums.val.length), nth nums i hi = c.val) :
    ∀ r : Std.I64, maximum_product nums k = ok r →
      r.val = (((c.val + (k.val.toNat / nums.val.length : ℕ) + 1) ^ (k.val.toNat % nums.val.length)) *
                 ((c.val + (k.val.toNat / nums.val.length : ℕ)) ^
                   (nums.val.length - k.val.toNat % nums.val.length))) % M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (c : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (hunif : ∀ (i : ℕ) (hi : i < nums.val.length), nth nums i hi = c.val), ∀ r : Std.I64, maximum_product nums k = ok r →
      r.val = (((c.val + (k.val.toNat / nums.val.length : ℕ) + 1) ^ (k.val.toNat % nums.val.length)) *
                 ((c.val + (k.val.toNat / nums.val.length : ℕ)) ^
                   (nums.val.length - k.val.toNat % nums.val.length))) % M) := by
  sorry

/-- Suppose n = len(nums) = 2. Write a = nums[0], b = nums[1], and S = a + b + k. Define P by: if a > b + k then P = a * (b + k); else if b > a + k then P = (a + k) * b; else P = floor(S^2 / 4). Whenever maximum_product(nums,k) returns r, r = P mod M, with the least nonnegative residue.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) (h2 : nums.val.length = 2) :
    ∀ r : Std.I64, maximum_product nums k = ok r →
      r.val = (let a := nth nums 0 (by omega)
               let b := nth nums 1 (by omega)
               if a > b + k.val then a * (b + k.val)
               else if b > a + k.val then (a + k.val) * b
               else (a + b + k.val) ^ 2 / 4) % M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) (h2 : nums.val.length = 2), ∀ r : Std.I64, maximum_product nums k = ok r →
      r.val = (let a := nth nums 0 (by omega)
               let b := nth nums 1 (by omega)
               if a > b + k.val then a * (b + k.val)
               else if b > a + k.val then (a + k.val) * b
               else (a + b + k.val) ^ 2 / 4) % M) := by
  sorry

/-- For every permutation sigma of the index set {0,...,n-1}, define nums' by nums'[i] = nums[sigma(i)] for 0 <= i < n. Whenever maximum_product(nums,k) returns r and maximum_product(nums',k) returns r', we have r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (σ : Equiv.Perm (Fin nums.val.length)) (nums' : Slice Std.I64)
    (hσ : IsPermuted nums nums' σ) :
    ∀ r r' : Std.I64, maximum_product nums k = ok r → maximum_product nums' k = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (σ : Equiv.Perm (Fin nums.val.length)) (nums' : Slice Std.I64)
    (hσ : IsPermuted nums nums' σ), ∀ r r' : Std.I64, maximum_product nums k = ok r → maximum_product nums' k = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let E be the maximum, over all integer vectors (d_0,...,d_{n-1}) with d_i >= 0 for every i and sum_{i=0}^{n-1} d_i = k, of the ordinary integer product product_{i=0}^{n-1} (nums[i] + d_i). Whenever maximum_product(nums,k) returns r, r is the least nonnegative residue of E modulo M.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (E : ℤ) (hE : IsMaxEq nums k.val E) :
    ∀ r : Std.I64, maximum_product nums k = ok r →
      0 ≤ r.val ∧ r.val < M ∧ r.val ≡ E [ZMOD M] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k)
    (E : ℤ) (hE : IsMaxEq nums k.val E), ∀ r : Std.I64, maximum_product nums k = ok r →
      0 ≤ r.val ∧ r.val < M ∧ r.val ≡ E [ZMOD M]) := by
  sorry

/-- For j in {1,2}, let P_j be the maximum, over all nonnegative integer vectors d = (d_0,...,d_{n-1}) with sum_{i=0}^{n-1} d_i <= k_j, of the ordinary integer product product_{i=0}^{n-1} (nums[i] + d_i). Then P_1 <= P_2. Moreover, if P_2 < M, then whenever the calls maximum_product(nums,k1) and maximum_product(nums,k2) return r1 and r2 respectively, we have r1 = P_1, r2 = P_2, and r1 <= r2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k1 <= k2 <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_9 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : ValidNums nums)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
    (P₁ P₂ : ℤ) (hP₁ : IsMaxLE nums k1.val P₁) (hP₂ : IsMaxLE nums k2.val P₂) :
    P₁ ≤ P₂ ∧
      (P₂ < M → ∀ r1 r2 : Std.I64,
        maximum_product nums k1 = ok r1 → maximum_product nums k2 = ok r2 →
          r1.val = P₁ ∧ r2.val = P₂ ∧ r1.val ≤ r2.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : ValidNums nums)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
    (P₁ P₂ : ℤ) (hP₁ : IsMaxLE nums k1.val P₁) (hP₂ : IsMaxLE nums k2.val P₂), P₁ ≤ P₂ ∧
      (P₂ < M → ∀ r1 r2 : Std.I64,
        maximum_product nums k1 = ok r1 → maximum_product nums k2 = ok r2 →
          r1.val = P₁ ∧ r2.val = P₂ ∧ r1.val ≤ r2.val)) := by
  sorry

/-- Let P be the maximum, over all nonnegative integer vectors d with sum_i d_i <= k, of product_{i=0}^{n-1} (nums[i] + d_i), and let P' be the analogous maximum with nums'[i] in place of nums[i]. Then P <= P'. Moreover, if P' < M, then whenever maximum_product(nums,k) returns r and maximum_product(nums',k) returns r', we have r = P, r' = P', and r <= r'.
  Preconditions: Let n = len(nums). Assume nums and nums' are slices of length n with 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= nums'[i] <= 1000000. Let k satisfy 1 <= k <= 100000 and M = 1000000007. -/
theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hlen : nums'.val.length = nums.val.length)
    (hle : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ nth nums i hi ∧ nth nums i hi ≤ nth nums' i (by omega) ∧
        nth nums' i (by omega) ≤ 1000000)
    (hk : ValidK k)
    (P P' : ℤ) (hP : IsMaxLE nums k.val P) (hP' : IsMaxLE nums' k.val P') :
    P ≤ P' ∧
      (P' < M → ∀ r r' : Std.I64,
        maximum_product nums k = ok r → maximum_product nums' k = ok r' →
          r.val = P ∧ r'.val = P' ∧ r.val ≤ r'.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hlen : nums'.val.length = nums.val.length)
    (hle : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ nth nums i hi ∧ nth nums i hi ≤ nth nums' i (by omega) ∧
        nth nums' i (by omega) ≤ 1000000)
    (hk : ValidK k)
    (P P' : ℤ) (hP : IsMaxLE nums k.val P) (hP' : IsMaxLE nums' k.val P'), P ≤ P' ∧
      (P' < M → ∀ r r' : Std.I64,
        maximum_product nums k = ok r → maximum_product nums' k = ok r' →
          r.val = P ∧ r'.val = P' ∧ r.val ≤ r'.val)) := by
  sorry

/-- Whenever maximum_product(nums,k) returns r, there exist nonnegative integers d_0,...,d_{n-1} with sum_{i=0}^{n-1} d_i <= k such that product_{i=0}^{n-1} (nums[i] + d_i) is congruent to r modulo M.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) :
    ∀ r : Std.I64, maximum_product nums k = ok r →
      ∃ d : Fin nums.val.length → ℤ,
        FeasibleLE nums.val.length k.val d ∧ prodAlloc nums d ≡ r.val [ZMOD M] := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k), ∀ r : Std.I64, maximum_product nums k = ok r →
      ∃ d : Fin nums.val.length → ℤ,
        FeasibleLE nums.val.length k.val d ∧ prodAlloc nums d ≡ r.val [ZMOD M]) := by
  sorry

/-- Let B = product_{i=0}^{n-1} nums[i] as an ordinary integer, and let P* be the maximum, over all nonnegative integer vectors d with sum_i d_i <= k, of product_{i=0}^{n-1} (nums[i] + d_i). Then P* > B. Consequently, if P* < M, then whenever maximum_product(nums,k) returns r, r = P* and r > B.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < n. Let M = 1000000007. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNumsPos nums) (hk : ValidK k)
    (P : ℤ) (hP : IsMaxLE nums k.val P) :
    baseProd nums < P ∧
      (P < M → ∀ r : Std.I64, maximum_product nums k = ok r →
        r.val = P ∧ baseProd nums < r.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNumsPos nums) (hk : ValidK k)
    (P : ℤ) (hP : IsMaxLE nums k.val P), baseProd nums < P ∧
      (P < M → ∀ r : Std.I64, maximum_product nums k = ok r →
        r.val = P ∧ baseProd nums < r.val)) := by
  sorry

/-- Whenever maximum_product(nums,k) returns r, there exist nonnegative integers d_0,...,d_{n-1} with sum_{i=0}^{n-1} d_i <= k such that product_{i=0}^{n-1} (nums[i] + d_i) is congruent to r modulo M, and for every nonnegative integer vector e = (e_0,...,e_{n-1}) with sum_{i=0}^{n-1} e_i <= k, product_{i=0}^{n-1} (nums[i] + e_i) <= product_{i=0}^{n-1} (nums[i] + d_i).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let M = 1000000007. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k) :
    ∀ r : Std.I64, maximum_product nums k = ok r →
      ∃ d : Fin nums.val.length → ℤ,
        FeasibleLE nums.val.length k.val d ∧ prodAlloc nums d ≡ r.val [ZMOD M] ∧
          ∀ e : Fin nums.val.length → ℤ,
            FeasibleLE nums.val.length k.val e → prodAlloc nums e ≤ prodAlloc nums d := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : ValidNums nums) (hk : ValidK k), ∀ r : Std.I64, maximum_product nums k = ok r →
      ∃ d : Fin nums.val.length → ℤ,
        FeasibleLE nums.val.length k.val d ∧ prodAlloc nums d ≡ r.val [ZMOD M] ∧
          ∀ e : Fin nums.val.length → ℤ,
            FeasibleLE nums.val.length k.val e → prodAlloc nums e ≤ prodAlloc nums d) := by
  sorry

end AegisSpec.MaximumProduct
