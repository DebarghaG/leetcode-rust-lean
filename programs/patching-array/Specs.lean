import Aegis.MinPatches.Code.Funs

/-!
# Specifications of `Aegis.MinPatches.min_patches`

LeetCode problem `patching-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinPatches

def contents (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def Nondecreasing (A : List ℤ) : Prop := A.Pairwise (fun x y => x ≤ y)

def Positive (A : List ℤ) : Prop := ∀ a ∈ A, 1 ≤ a

def Covers (A : List ℤ) (n : ℤ) : Prop :=
  ∀ x : ℤ, 1 ≤ x → x ≤ n → ∃ I : Finset (Fin A.length), I.sum (fun i => A.get i) = x

def Occurs (A : List ℤ) (v : ℤ) : Prop := v ∈ A

def countOf (A : List ℤ) (v : ℤ) : ℕ := A.countP (fun a => decide (a = v))

def SubMultiset (A B : List ℤ) : Prop := ∀ v : ℤ, countOf A v ≤ countOf B v

def powCov (k : ℕ) : ℤ := ((2 : ℕ) ^ k : ℤ) - 1

theorem powCov_exists (n : ℤ) : ∃ k : ℕ, n ≤ powCov k := by
  rcases Int.lt_or_le n 0 with h | h
  · exact ⟨0, by simp [powCov]; omega⟩
  · refine ⟨n.toNat + 1, ?_⟩
    have h1 : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n
    have h2 : ((n.toNat : ℕ) : ℤ) + 1 ≤ ((2 : ℕ) ^ (n.toNat + 1) : ℤ) := by
      have : n.toNat + 1 ≤ 2 ^ (n.toNat + 1) := by
        have := Nat.lt_two_pow_self (n := n.toNat + 1)
        omega
      exact_mod_cast this
    have h3 : n ≤ ((2 : ℕ) ^ (n.toNat + 1) : ℤ) - 1 := by omega
    simpa [powCov] using h3

def L (n : ℤ) : ℤ := (Nat.find (powCov_exists n) : ℤ)

/-- Define a finite list A of positive integers to cover [1,n] iff, for every integer x with 1 <= x <= n, there is a subset I of the index set {0,...,len(A)-1} such that the sum of A[i] over i in I equals x, with each index used at most once. Whenever the function returns a result r, r is the least integer k >= 0 for which there exists a finite list P of positive integers with len(P)=k such that nums followed by P covers [1,n]. Equivalently, such a P exists for k=r, and no list P' of positive integers with len(P') < r makes nums followed by P' cover [1,n].
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_1
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      0 ≤ r.val ∧
        (∃ P : List ℤ, (P.length : ℤ) = r.val ∧ Positive P ∧
          Covers (contents nums ++ P) n.val) ∧
        (∀ P : List ℤ, Positive P → (P.length : ℤ) < r.val →
          ¬ Covers (contents nums ++ P) n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      0 ≤ r.val ∧
        (∃ P : List ℤ, (P.length : ℤ) = r.val ∧ Positive P ∧
          Covers (contents nums ++ P) n.val) ∧
        (∀ P : List ℤ, Positive P → (P.length : ℤ) < r.val →
          ¬ Covers (contents nums ++ P) n.val)) := by
  sorry

/-- The function returns a result r; it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_2
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1) :
    ∃ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1), ∃ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r) := by
  sorry

/-- Let L(n) be the least integer k >= 0 such that 2^k - 1 >= n. Whenever the function returns a result r, 0 <= r <= L(n).
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_3
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → 0 ≤ r.val ∧ r.val ≤ L n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → 0 ≤ r.val ∧ r.val ≤ L n.val) := by
  sorry

/-- Define a list A of positive integers to cover [1,n] iff every integer x with 1 <= x <= n is the sum of some subset of the indices of A, each index used at most once. Whenever the function returns a result r, r = 0 if and only if nums itself covers [1,n].
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_4
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      (r.val = 0 ↔ Covers (contents nums) n.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      (r.val = 0 ↔ Covers (contents nums) n.val)) := by
  sorry

/-- If n=1, then whenever the function returns a result r, r = 0 if there exists an index i with nums[i]=1, and r = 1 otherwise.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_5
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hn1 : n.val = 1) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      ((Occurs (contents nums) 1 → r.val = 0) ∧
        (¬ Occurs (contents nums) 1 → r.val = 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hn1 : n.val = 1), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      ((Occurs (contents nums) 1 → r.val = 0) ∧
        (¬ Occurs (contents nums) 1 → r.val = 1))) := by
  sorry

/-- If len(nums)=1 and nums[0]=1, then whenever the function returns a result r, r is the least integer k >= 0 such that 2^(k+1) - 1 >= n.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_6
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hnums : nums.val = [1#i64]) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → r.val + 1 = L n.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hnums : nums.val = [1#i64]), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → r.val + 1 = L n.val) := by
  sorry

/-- If len(nums)=0, or (len(nums)>0 and nums[0]>n), then whenever the function returns a result r, r is the least integer k >= 0 such that 2^k - 1 >= n.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_7
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hcase : nums.val = [] ∨ ∃ (a : ℤ) (rest : List ℤ), contents nums = a :: rest ∧ n.val < a) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → r.val = L n.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hcase : nums.val = [] ∨ ∃ (a : ℤ) (rest : List ℤ), contents nums = a :: rest ∧ n.val < a), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → r.val = L n.val) := by
  sorry

/-- Let nums' be the subsequence of nums consisting of exactly those entries nums[i] with nums[i] <= n. Whenever the calls min_patches(nums,n) and min_patches(nums',n) return results r and r', respectively, we have r = r'.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_8
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (nums' : Slice Std.I64)
    (hnums' : nums'.val = nums.val.filter (fun x => decide (x.val ≤ n.val))) :
    ∀ (r r' : Std.I64),
      Aegis.MinPatches.min_patches nums n = ok r →
        Aegis.MinPatches.min_patches nums' n = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (nums' : Slice Std.I64)
    (hnums' : nums'.val = nums.val.filter (fun x => decide (x.val ≤ n.val))), ∀ (r r' : Std.I64),
      Aegis.MinPatches.min_patches nums n = ok r →
        Aegis.MinPatches.min_patches nums' n = ok r' → r = r') := by
  sorry

/-- Whenever the calls min_patches(nums,n) and min_patches(nums',n) return results r and r', respectively, we have r' <= r.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. Also nums' is another sorted slice satisfying the same constraints, and the multiset of entries of nums' contains the multiset of entries of nums. -/
theorem spec_9
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (nums' : Slice Std.I64)
    (hlen' : nums'.val.length ≤ 1000)
    (hsorted' : Nondecreasing (contents nums'))
    (helems' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hsub : SubMultiset (contents nums) (contents nums')) :
    ∀ (r r' : Std.I64),
      Aegis.MinPatches.min_patches nums n = ok r →
        Aegis.MinPatches.min_patches nums' n = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (nums' : Slice Std.I64)
    (hlen' : nums'.val.length ≤ 1000)
    (hsorted' : Nondecreasing (contents nums'))
    (helems' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hsub : SubMultiset (contents nums) (contents nums')), ∀ (r r' : Std.I64),
      Aegis.MinPatches.min_patches nums n = ok r →
        Aegis.MinPatches.min_patches nums' n = ok r' → r'.val ≤ r.val) := by
  sorry

/-- Whenever the calls min_patches(nums,n1) and min_patches(nums,n2) return results r1 and r2, respectively, we have r1 <= r2.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n1,n2 are i64s with 1 <= n1 <= n2 <= 2^31 - 1. -/
theorem spec_10
    (nums : Slice Std.I64) (n1 n2 : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 2 ^ 31 - 1) :
    ∀ (r1 r2 : Std.I64),
      Aegis.MinPatches.min_patches nums n1 = ok r1 →
        Aegis.MinPatches.min_patches nums n2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (n1 n2 : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 2 ^ 31 - 1), ∀ (r1 r2 : Std.I64),
      Aegis.MinPatches.min_patches nums n1 = ok r1 →
        Aegis.MinPatches.min_patches nums n2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Define a list A to cover [1,n] iff every integer x with 1 <= x <= n is the sum of some subset of the indices of A, each index used at most once. Whenever the function returns a result r, there exists a list P of positive integers such that len(P)=r, every element of P is at most n, and nums followed by P covers [1,n].
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_11
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      ∃ P : List ℤ, (P.length : ℤ) = r.val ∧ (∀ p ∈ P, 1 ≤ p ∧ p ≤ n.val) ∧
        Covers (contents nums ++ P) n.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      ∃ P : List ℤ, (P.length : ℤ) = r.val ∧ (∀ p ∈ P, 1 ≤ p ∧ p ≤ n.val) ∧
        Covers (contents nums ++ P) n.val) := by
  sorry

/-- Suppose n=2. Let c1 be the number of indices i with nums[i]=1, and let c2 be the number of indices i with nums[i]=2. Whenever the function returns a result r, the following holds: if c1 >= 1 and (c1 >= 2 or c2 >= 1), then r=0; otherwise, if c1 >= 1 or c2 >= 1, then r=1; otherwise r=2.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. -/
theorem spec_12
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hn2 : n.val = 2) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      ((1 ≤ countOf (contents nums) 1 ∧ (2 ≤ countOf (contents nums) 1 ∨
            1 ≤ countOf (contents nums) 2)) → r.val = 0) ∧
        (¬ (1 ≤ countOf (contents nums) 1 ∧ (2 ≤ countOf (contents nums) 1 ∨
              1 ≤ countOf (contents nums) 2)) →
          (1 ≤ countOf (contents nums) 1 ∨ 1 ≤ countOf (contents nums) 2) → r.val = 1) ∧
        (¬ (1 ≤ countOf (contents nums) 1 ∨ 1 ≤ countOf (contents nums) 2) → r.val = 2) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hn2 : n.val = 2), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r →
      ((1 ≤ countOf (contents nums) 1 ∧ (2 ≤ countOf (contents nums) 1 ∨
            1 ≤ countOf (contents nums) 2)) → r.val = 0) ∧
        (¬ (1 ≤ countOf (contents nums) 1 ∧ (2 ≤ countOf (contents nums) 1 ∨
              1 ≤ countOf (contents nums) 2)) →
          (1 ≤ countOf (contents nums) 1 ∨ 1 ≤ countOf (contents nums) 2) → r.val = 1) ∧
        (¬ (1 ≤ countOf (contents nums) 1 ∨ 1 ≤ countOf (contents nums) 2) → r.val = 2)) := by
  sorry

/-- Let L(n) be the least integer k >= 0 such that 2^k - 1 >= n. Whenever the function returns a result r, r <= L(n) - 1.
  Preconditions: nums is a slice of i64 with 0 <= len(nums) <= 1000; nums is sorted in nondecreasing order; every element nums[i] satisfies 1 <= nums[i] <= 10^4; and n is an i64 with 1 <= n <= 2^31 - 1. Assume also that there exists an index i with nums[i]=1. -/
theorem spec_13
    (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hone : Occurs (contents nums) 1) :
    ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → r.val ≤ L n.val - 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Std.I64)
    (hlen : nums.val.length ≤ 1000)
    (hsorted : Nondecreasing (contents nums))
    (helems : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10000)
    (hn : 1 ≤ n.val ∧ n.val ≤ 2 ^ 31 - 1)
    (hone : Occurs (contents nums) 1), ∀ r : Std.I64, Aegis.MinPatches.min_patches nums n = ok r → r.val ≤ L n.val - 1) := by
  sorry

end AegisSpec.MinPatches
