import Aegis.FindValidSplit.Code.Funs

/-!
# Specifications of `Aegis.FindValidSplit.find_valid_split`

LeetCode problem `split-the-array-to-make-coprime-products`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindValidSplit

  def valAt (nums : Slice I64) (k : ℕ) : ℤ :=
    if h : k < nums.val.length then (nums.val.get ⟨k, h⟩).val else 0

  def LeftProd (nums : Slice I64) (i : ℕ) : ℤ :=
    ((nums.val.take (i + 1)).map (fun x => x.val)).prod

  def RightProd (nums : Slice I64) (i : ℕ) : ℤ :=
    ((nums.val.drop (i + 1)).map (fun x => x.val)).prod

  def ValidSplit (nums : Slice I64) (i : ℕ) : Prop :=
    Int.gcd (LeftProd nums i) (RightProd nums i) = 1

  def SamePrimeDivisors (a b : ℤ) : Prop :=
    ∀ p : ℕ, p.Prime → ((p : ℤ) ∣ a ↔ (p : ℤ) ∣ b)

  /-- Let n = len(nums). For an index i with 0 <= i <= n-2, define L(i) = nums[0] * nums[1] * ... * nums[i] and R(i) = nums[i+1] * ... * nums[n-1] as mathematical integer products. Whenever the function returns a result r, the following holds: if there exists i with 0 <= i <= n-2 and gcd(L(i), R(i)) = 1, then r is the least such i (0 <= r <= n-2, gcd(L(r), R(r)) = 1, and for every j with 0 <= j < r, gcd(L(j), R(j)) > 1); if no such i exists, then r = -1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_1 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r) :
      ((∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i) →
        ∃ i : ℕ, r.val = (i : ℤ) ∧ i + 2 ≤ nums.val.length ∧ ValidSplit nums i ∧
          ∀ j : ℕ, j < i → 1 < Int.gcd (LeftProd nums j) (RightProd nums j)) ∧
      ((¬ ∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r), ((∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i) →
          ∃ i : ℕ, r.val = (i : ℤ) ∧ i + 2 ≤ nums.val.length ∧ ValidSplit nums i ∧
            ∀ j : ℕ, j < i → 1 < Int.gcd (LeftProd nums j) (RightProd nums j)) ∧
        ((¬ ∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i) → r.val = -1)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, or access an out-of-bounds index.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_2 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6) :
      ∃ r : I64, Aegis.FindValidSplit.find_valid_split nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6), ∃ r : I64, Aegis.FindValidSplit.find_valid_split nums = ok r) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r, either r = -1 or 0 <= r <= n-2. Equivalently, -1 <= r <= n-2.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_3 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r) :
      -1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r), -1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 2) := by
    sorry

  /-- Let n = len(nums). For 0 <= i <= n-2 let L(i) and R(i) be the mathematical products of nums[0..i] and nums[i+1..n-1]. Whenever the function returns a result r with r != -1, the split at r is valid: 0 <= r <= n-2 and gcd(L(r), R(r)) = 1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_4 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
      (hrne : r.val ≠ -1) :
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 2 ∧ ValidSplit nums r.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
        (hrne : r.val ≠ -1), 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 2 ∧ ValidSplit nums r.val.toNat) := by
    sorry

  /-- Let n = len(nums). For 0 <= i <= n-2 let L(i) and R(i) be the mathematical products of nums[0..i] and nums[i+1..n-1]. Whenever the function returns a result r with r != -1, every earlier split is invalid: for every j with 0 <= j < r, gcd(L(j), R(j)) > 1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_5 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
      (hrne : r.val ≠ -1) :
      ∀ j : ℕ, (j : ℤ) < r.val → 1 < Int.gcd (LeftProd nums j) (RightProd nums j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
        (hrne : r.val ≠ -1), ∀ j : ℕ, (j : ℤ) < r.val → 1 < Int.gcd (LeftProd nums j) (RightProd nums j)) := by
    sorry

  /-- Let n = len(nums). For 0 <= i <= n-2 let L(i) and R(i) be the mathematical products of nums[0..i] and nums[i+1..n-1]. Whenever the function returns a result r, r = -1 if and only if there is no index i with 0 <= i <= n-2 and gcd(L(i), R(i)) = 1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_6 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r) :
      (r.val = -1 ↔ ¬ ∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r), (r.val = -1 ↔ ¬ ∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i)) := by
    sorry

  /-- Let n = len(nums). For 0 <= i <= n-2 let L(i) and R(i) be the mathematical products of nums[0..i] and nums[i+1..n-1]. Whenever the function returns a result r, if there exists a valid split i (that is, 0 <= i <= n-2 and gcd(L(i), R(i)) = 1), then r != -1 and r <= i for every such valid split i.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_7 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
      (hexists : ∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i) :
      r.val ≠ -1 ∧ ∀ i : ℕ, i + 2 ≤ nums.val.length → ValidSplit nums i → r.val ≤ (i : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
        (hexists : ∃ i : ℕ, i + 2 ≤ nums.val.length ∧ ValidSplit nums i), r.val ≠ -1 ∧ ∀ i : ℕ, i + 2 ≤ nums.val.length → ValidSplit nums i → r.val ≤ (i : ℤ)) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r with r != -1, every element on the left of the split is coprime to every element on the right: for every a with 0 <= a <= r and every b with r < b < n, gcd(nums[a], nums[b]) = 1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_8 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
      (hrne : r.val ≠ -1) :
      ∀ a b : ℕ, (a : ℤ) ≤ r.val → r.val < (b : ℤ) → b < nums.val.length →
        Int.gcd (valAt nums a) (valAt nums b) = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
        (hrne : r.val ≠ -1), ∀ a b : ℕ, (a : ℤ) ≤ r.val → r.val < (b : ℤ) → b < nums.val.length →
          Int.gcd (valAt nums a) (valAt nums b) = 1) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r = -1, every split fails: for every i with 0 <= i <= n-2 there exist indices a and b with 0 <= a <= i < b < n and gcd(nums[a], nums[b]) > 1.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. -/
  theorem spec_9 (nums : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
      (hrm1 : r.val = -1) :
      ∀ i : ℕ, i + 2 ≤ nums.val.length →
        ∃ a b : ℕ, a ≤ i ∧ i < b ∧ b < nums.val.length ∧
          1 < Int.gcd (valAt nums a) (valAt nums b) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (r : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
        (hrm1 : r.val = -1), ∀ i : ℕ, i + 2 ≤ nums.val.length →
          ∃ a b : ℕ, a ≤ i ∧ i < b ∧ b < nums.val.length ∧
            1 < Int.gcd (valAt nums a) (valAt nums b)) := by
    sorry

  /-- Whenever find_valid_split(nums) returns a result r and find_valid_split(nums') returns a result r', we have r = r'.
    Preconditions: Let n = len(nums). The slice nums satisfies 1 <= n <= 10^4 and, for every k with 0 <= k < n, 1 <= nums[k] <= 10^6. Let nums' be any slice such that len(nums') = n and, for every k with 0 <= k < n, 1 <= nums'[k] <= 10^6 and nums'[k] has exactly the same set of prime divisors as nums[k]. -/
  theorem spec_10 (nums nums' : Slice I64)
      (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (hpre' : 1 ≤ nums'.val.length ∧ nums'.val.length ≤ 10 ^ 4 ∧
        ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
      (hlen : nums'.val.length = nums.val.length)
      (hpd : ∀ k : ℕ, k < nums.val.length → SamePrimeDivisors (valAt nums k) (valAt nums' k))
      (r r' : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
      (hr' : Aegis.FindValidSplit.find_valid_split nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hpre : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (hpre' : 1 ≤ nums'.val.length ∧ nums'.val.length ≤ 10 ^ 4 ∧
          ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 6)
        (hlen : nums'.val.length = nums.val.length)
        (hpd : ∀ k : ℕ, k < nums.val.length → SamePrimeDivisors (valAt nums k) (valAt nums' k))
        (r r' : I64) (hr : Aegis.FindValidSplit.find_valid_split nums = ok r)
        (hr' : Aegis.FindValidSplit.find_valid_split nums' = ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.FindValidSplit
