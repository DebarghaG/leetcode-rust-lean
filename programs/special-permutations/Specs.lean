import Aegis.SpecialPerm.Code.Funs

/-!
# Specifications of `Aegis.SpecialPerm.special_perm`

LeetCode problem `special-permutations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SpecialPerm

namespace AegisSpec.SpecialPerm

noncomputable section

def modulus : ℤ := 1000000007

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def len (nums : Slice I64) : ℕ := nums.val.length

def valAt (nums : Slice I64) (i : ℕ) : ℤ :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def Comparable (a b : ℤ) : Prop := a ∣ b ∨ b ∣ a

def ChainDiv : List ℤ → Prop
  | a :: b :: bs => Comparable a b ∧ ChainDiv (b :: bs)
  | _ => True

def IsSpecialPerm (l p : List ℤ) : Prop := p.Perm l ∧ ChainDiv p

def specialCount (nums : Slice I64) : ℕ :=
  Nat.card {p : List ℤ // IsSpecialPerm (vals nums) p}

def Incomparable (nums : Slice I64) (i j : ℕ) : Prop :=
  ¬ Comparable (valAt nums i) (valAt nums j)

def Valid (nums : Slice I64) : Prop :=
  2 ≤ len nums ∧ len nums ≤ 14 ∧ (∀ x ∈ nums.val, 0 < x.val) ∧ nums.val.Nodup

def Bounded (nums : Slice I64) : Prop := ∀ x ∈ nums.val, x.val ≤ 1000000000

/-- Let M = 1000000007. Whenever the function returns a result r, r is the remainder modulo M of the number of special permutations of nums: that is, the number of sequences p of length n such that (a) p is a permutation of nums (each value of nums occurs in p exactly once), and (b) for every i with 0 <= i < n-1, either p[i] divides p[i+1] or p[i+1] divides p[i]. Equivalently, 0 <= r < M and r is congruent modulo M to that exact count T.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct (hence 1 <= nums[i] <= 10^9 under the problem constraints). -/
theorem spec_1 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r) :
    0 ≤ r.val ∧ r.val < modulus ∧ r.val = (specialCount nums : ℤ) % modulus := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r), 0 ≤ r.val ∧ r.val < modulus ∧ r.val = (specialCount nums : ℤ) % modulus) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_2 (nums : Slice I64) (hv : Valid nums) :
    ∃ r : I64, special_perm nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hv : Valid nums), ∃ r : I64, special_perm nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= n!, where n! = 1*2*...*n.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_3 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r) :
    r.val ≤ (Nat.factorial (len nums) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r), r.val ≤ (Nat.factorial (len nums) : ℤ)) := by
  sorry

/-- For every valid nums with len(nums) = 2, whenever the function returns a result r: if nums[0] divides nums[1] or nums[1] divides nums[0], then r = 2; otherwise r = 0.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_4 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hlen : len nums = 2) (h : special_perm nums = ok r) :
    (Comparable (valAt nums 0) (valAt nums 1) → r.val = 2) ∧
      (¬ Comparable (valAt nums 0) (valAt nums 1) → r.val = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hlen : len nums = 2) (h : special_perm nums = ok r), (Comparable (valAt nums 0) (valAt nums 1) → r.val = 2) ∧
      (¬ Comparable (valAt nums 0) (valAt nums 1) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, if for every pair of indices i,j with 0 <= i < n, 0 <= j < n, and i != j, either nums[i] divides nums[j] or nums[j] divides nums[i], then r = (n! mod 1000000007).
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_5 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hcomp : ∀ i j : ℕ, i < len nums → j < len nums → i ≠ j →
      Comparable (valAt nums i) (valAt nums j))
    (h : special_perm nums = ok r) :
    r.val = ((Nat.factorial (len nums) % 1000000007 : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hcomp : ∀ i j : ℕ, i < len nums → j < len nums → i ≠ j →
      Comparable (valAt nums i) (valAt nums j))
    (h : special_perm nums = ok r), r.val = ((Nat.factorial (len nums) % 1000000007 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if for every pair of distinct indices i,j with 0 <= i < n, 0 <= j < n, and i != j, neither nums[i] divides nums[j] nor nums[j] divides nums[i], then r = 0.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_6 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hnc : ∀ i j : ℕ, i < len nums → j < len nums → i ≠ j →
      Incomparable nums i j)
    (h : special_perm nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hnc : ∀ i j : ℕ, i < len nums → j < len nums → i ≠ j →
      Incomparable nums i j)
    (h : special_perm nums = ok r), r.val = 0) := by
  sorry

/-- For every valid nums and every slice q of length n that is a permutation of nums (for every integer v, v occurs in q exactly as many times as in nums), if the call special_perm(nums) returns r and the call special_perm(q) returns r', then r = r'.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_7 (nums q : Slice I64) (hv : Valid nums)
    (hlen : len q = len nums)
    (hperm : ∀ v : ℤ, (vals q).count v = (vals nums).count v)
    (r r' : I64) (h : special_perm nums = ok r) (h' : special_perm q = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums q : Slice I64) (hv : Valid nums)
    (hlen : len q = len nums)
    (hperm : ∀ v : ℤ, (vals q).count v = (vals nums).count v)
    (r r' : I64) (h : special_perm nums = ok r) (h' : special_perm q = ok r'), r = r') := by
  sorry

/-- For every valid nums and every positive integer c such that c*nums[i] <= 10^9 for every i with 0 <= i < n, let q be the slice with q[i] = c*nums[i]. If special_perm(nums) returns r and special_perm(q) returns r', then r = r'.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_8 (nums q : Slice I64) (c : ℤ) (hv : Valid nums) (hc : 0 < c)
    (hbnd : ∀ i : ℕ, i < len nums → c * valAt nums i ≤ 1000000000)
    (hlen : len q = len nums)
    (hq : ∀ i : ℕ, i < len nums → valAt q i = c * valAt nums i)
    (r r' : I64) (h : special_perm nums = ok r) (h' : special_perm q = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums q : Slice I64) (c : ℤ) (hv : Valid nums) (hc : 0 < c)
    (hbnd : ∀ i : ℕ, i < len nums → c * valAt nums i ≤ 1000000000)
    (hlen : len q = len nums)
    (hq : ∀ i : ℕ, i < len nums → valAt q i = c * valAt nums i)
    (r r' : I64) (h : special_perm nums = ok r) (h' : special_perm q = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exists at least one special permutation of nums.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_9 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r) (hr : 0 < r.val) :
    ∃ p : List ℤ, IsSpecialPerm (vals nums) p := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r) (hr : 0 < r.val), ∃ p : List ℤ, IsSpecialPerm (vals nums) p) := by
  sorry

/-- For every valid nums with 2 <= len(nums) <= 12, whenever the function returns a result r, r is an even integer.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_10 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hlen : len nums ≤ 12) (h : special_perm nums = ok r) :
    (2 : ℤ) ∣ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hlen : len nums ≤ 12) (h : special_perm nums = ok r), (2 : ℤ) ∣ r.val) := by
  sorry

/-- Whenever the function returns a result r, if there exist distinct indices i,j with 0 <= i < n and 0 <= j < n such that neither nums[i] divides nums[j] nor nums[j] divides nums[i], then, writing T for the exact number of special permutations of nums and n! = 1*2*...*n, there is a nonnegative integer q with T = q*1000000007 + r and T <= n! - 2*(n-1)!.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_11 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hincomp : ∃ i j : ℕ, i < len nums ∧ j < len nums ∧ i ≠ j ∧ Incomparable nums i j)
    (h : special_perm nums = ok r) :
    ∃ q : ℕ, (specialCount nums : ℤ) = (q : ℤ) * 1000000007 + r.val ∧
      (specialCount nums : ℤ) ≤
        (Nat.factorial (len nums) : ℤ) - 2 * (Nat.factorial (len nums - 1) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (hincomp : ∃ i j : ℕ, i < len nums ∧ j < len nums ∧ i ≠ j ∧ Incomparable nums i j)
    (h : special_perm nums = ok r), ∃ q : ℕ, (specialCount nums : ℤ) = (q : ℤ) * 1000000007 + r.val ∧
      (specialCount nums : ℤ) ≤
        (Nat.factorial (len nums) : ℤ) - 2 * (Nat.factorial (len nums - 1) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let T be the exact number of special permutations of nums. Then there exists a nonnegative integer q such that T = q*1000000007 + r and T is even.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is positive and all entries are distinct. -/
theorem spec_12 (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r) :
    ∃ q : ℕ, (specialCount nums : ℤ) = (q : ℤ) * 1000000007 + r.val ∧
      2 ∣ specialCount nums := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums)
    (h : special_perm nums = ok r), ∃ q : ℕ, (specialCount nums : ℤ) = (q : ℤ) * 1000000007 + r.val ∧
      2 ∣ specialCount nums) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is a positive integer with 1 <= nums[i] <= 10^9, and all entries are distinct; there exists an index i with 0 <= i < n such that for every j with 0 <= j < n and j != i, neither nums[i] divides nums[j] nor nums[j] divides nums[i]. -/
theorem spec_13 (nums : Slice I64) (r : I64) (hv : Valid nums) (hb : Bounded nums)
    (hiso : ∃ i : ℕ, i < len nums ∧ ∀ j : ℕ, j < len nums → j ≠ i → Incomparable nums i j)
    (h : special_perm nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums) (hb : Bounded nums)
    (hiso : ∃ i : ℕ, i < len nums ∧ ∀ j : ℕ, j < len nums → j ≠ i → Incomparable nums i j)
    (h : special_perm nums = ok r), r.val = 0) := by
  sorry

/-- Let T be the exact number of special permutations of nums. Whenever the function returns a result r, T = n! - 2*(n-1)! and consequently r = (n! - 2*(n-1)!) mod 1000000007.
  Preconditions: nums is a slice of 64-bit integers; n = len(nums); 2 <= n <= 14; every nums[i] is a positive integer with 1 <= nums[i] <= 10^9, and all entries are distinct; there is a unique unordered pair of distinct indices {i, j} such that neither nums[i] divides nums[j] nor nums[j] divides nums[i], and every other unordered pair of distinct indices is comparable by divisibility. -/
theorem spec_14 (nums : Slice I64) (r : I64) (hv : Valid nums) (hb : Bounded nums)
    (huniq : ∃ i j : ℕ, i < len nums ∧ j < len nums ∧ i < j ∧ Incomparable nums i j ∧
      ∀ i' j' : ℕ, i' < len nums → j' < len nums → i' ≠ j' →
        ¬ Incomparable nums i' j' ∨ (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i))
    (h : special_perm nums = ok r) :
    (specialCount nums : ℤ) =
        (Nat.factorial (len nums) : ℤ) - 2 * (Nat.factorial (len nums - 1) : ℤ) ∧
      r.val = (((Nat.factorial (len nums) - 2 * Nat.factorial (len nums - 1)) % 1000000007
        : ℕ) : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (r : I64) (hv : Valid nums) (hb : Bounded nums)
    (huniq : ∃ i j : ℕ, i < len nums ∧ j < len nums ∧ i < j ∧ Incomparable nums i j ∧
      ∀ i' j' : ℕ, i' < len nums → j' < len nums → i' ≠ j' →
        ¬ Incomparable nums i' j' ∨ (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i))
    (h : special_perm nums = ok r), (specialCount nums : ℤ) =
        (Nat.factorial (len nums) : ℤ) - 2 * (Nat.factorial (len nums - 1) : ℤ) ∧
      r.val = (((Nat.factorial (len nums) - 2 * Nat.factorial (len nums - 1)) % 1000000007
        : ℕ) : ℤ)) := by
  sorry

end

end AegisSpec.SpecialPerm
