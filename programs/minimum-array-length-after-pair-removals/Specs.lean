import Aegis.MinLengthAfterRemovals.Code.Funs

/-!
# Specifications of `Aegis.MinLengthAfterRemovals.min_length_after_removals`

LeetCode problem `minimum-array-length-after-pair-removals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinLengthAfterRemovals

def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : ℕ := (contents nums).length

def cnt (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  ((contents nums).filter (fun x => x = v)).length

def maxMult (nums : Slice Std.I64) : ℕ :=
  ((contents nums).map (fun v => cnt nums v)).foldr max 0

def EntriesInRange (l : List ℤ) : Prop := ∀ x ∈ l, 1 ≤ x ∧ x ≤ 1000000000

def Sorted (l : List ℤ) : Prop :=
  ∀ (i j : ℕ) (x y : ℤ), l[i]? = some x → l[j]? = some y → i < j → x ≤ y

def AllEqual (l : List ℤ) : Prop := ∀ x ∈ l, ∀ y ∈ l, x = y

def PairwiseDistinct (l : List ℤ) : Prop :=
  ∀ (i j : ℕ) (x y : ℤ), l[i]? = some x → l[j]? = some y → i < j → x ≠ y

def Removable (l l' : List ℤ) : Prop :=
  ∃ (i j : ℕ) (x y : ℤ), l[i]? = some x ∧ l[j]? = some y ∧ i < j ∧ x < y ∧
    l' = (l.eraseIdx j).eraseIdx i

def RemovalSeq : ℕ → List ℤ → List ℤ → Prop
  | 0, l, l' => l' = l
  | k + 1, l, l' => ∃ m, Removable l m ∧ RemovalSeq k m l'

def IsMatching (l : List ℤ) (m : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ m, ∃ x y : ℤ, l[p.1]? = some x ∧ l[p.2]? = some y ∧ p.1 < p.2 ∧ x < y) ∧
    (m.biUnion (fun p => ({p.1, p.2} : Finset ℕ))).card = 2 * m.card

noncomputable def maxMatchingSize (l : List ℤ) : ℕ := by
  classical
  exact (((Finset.range l.length).product (Finset.range l.length)).powerset.filter
    (IsMatching l)).sup Finset.card

/-- Let n = len(nums) and let M be the maximum multiplicity in nums, i.e. M = max{ cnt(v) | v occurs in nums }, where cnt(v) = |{ i | 0 <= i < n and nums[i] = v }|. The call returns a result r and r = 2*M - n if 2*M > n, while r = n mod 2 if 2*M <= n. Here n mod 2 is 0 when n is even and 1 when n is odd.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∃ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r ∧
      r.val = (if 2 * (maxMult nums : ℤ) > (len nums : ℤ)
               then 2 * (maxMult nums : ℤ) - (len nums : ℤ)
               else (len nums : ℤ) % 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∃ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r ∧
      r.val = (if 2 * (maxMult nums : ℤ) > (len nums : ℤ)
               then 2 * (maxMult nums : ℤ) - (len nums : ℤ)
               else (len nums : ℤ) % 2)) := by
  sorry

/-- For every nums satisfying the preconditions, the call does not fail: there exists an integer r such that min_length_after_removals(nums) = Result.ok r. In particular, no overflow, out-of-bounds access, or panic occurs.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∃ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∃ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r) := by
  sorry

/-- Whenever the call returns a result r, 0 <= r <= len(nums).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (len nums : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (len nums : ℤ)) := by
  sorry

/-- Whenever the call returns a result r, r mod 2 = len(nums) mod 2. Equivalently, r is congruent to len(nums) modulo 2.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      r.val % 2 = (len nums : ℤ) % 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      r.val % 2 = (len nums : ℤ) % 2) := by
  sorry

/-- Let n = len(nums) and let M be the maximum multiplicity in nums. Whenever the call returns a result r, r >= 2*M - n. Equivalently, at least the surplus of the most frequent value over all other values combined cannot be removed.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      2 * (maxMult nums : ℤ) - (len nums : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      2 * (maxMult nums : ℤ) - (len nums : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(nums) and let P be the maximum size of a set of pairwise disjoint unordered pairs {i,j} such that 0 <= i < j < n and nums[i] < nums[j]. Whenever the call returns a result r, r = n - 2*P.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      r.val = (len nums : ℤ) - 2 * (maxMatchingSize (contents nums) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      r.val = (len nums : ℤ) - 2 * (maxMatchingSize (contents nums) : ℤ)) := by
  sorry

/-- Whenever the call returns a result r, for every integer k >= 0 and every sequence of k valid removal operations applied to nums, the length after those operations, len(nums) - 2*k, is at least r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      ∀ k : ℕ, (∃ l' : List ℤ, RemovalSeq k (contents nums) l') →
        r.val ≤ (len nums : ℤ) - 2 * (k : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      ∀ k : ℕ, (∃ l' : List ℤ, RemovalSeq k (contents nums) l') →
        r.val ≤ (len nums : ℤ) - 2 * (k : ℤ)) := by
  sorry

/-- Whenever the call returns a result r, len(nums) - r is even, and there exists a sequence of exactly (len(nums) - r)/2 valid removal operations applied to nums that leaves exactly r elements.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      ∃ k : ℕ, (len nums : ℤ) - r.val = 2 * (k : ℤ) ∧
        ∃ l' : List ℤ, RemovalSeq k (contents nums) l' ∧ (l'.length : ℤ) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      ∃ k : ℕ, (len nums : ℤ) - r.val = 2 * (k : ℤ) ∧
        ∃ l' : List ℤ, RemovalSeq k (contents nums) l' ∧ (l'.length : ℤ) = r.val) := by
  sorry

/-- Whenever the call returns a result r, r = len(nums) if and only if every element of nums is equal.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      (r.val = (len nums : ℤ) ↔ AllEqual (contents nums)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      (r.val = (len nums : ℤ) ↔ AllEqual (contents nums))) := by
  sorry

/-- Whenever the call returns a result r, if the entries of nums are pairwise distinct (nums[i] != nums[j] for every 0 <= i < j < len(nums)), then r = len(nums) mod 2.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      PairwiseDistinct (contents nums) → r.val = (len nums : ℤ) % 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      PairwiseDistinct (contents nums) → r.val = (len nums : ℤ) % 2) := by
  sorry

/-- Let n = len(nums) and let M be the maximum multiplicity in nums. Whenever the call returns a result r, r = 0 if and only if n is even and 2*M <= n.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      (r.val = 0 ↔ (len nums : ℤ) % 2 = 0 ∧ 2 * (maxMult nums : ℤ) ≤ (len nums : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      (r.val = 0 ↔ (len nums : ℤ) % 2 = 0 ∧ 2 * (maxMult nums : ℤ) ≤ (len nums : ℤ))) := by
  sorry

/-- Let n = len(nums), n2 = len(nums2), and let M(nums) be the maximum multiplicity in nums (similarly for nums2). If n = n2 and M(nums) = M(nums2), then min_length_after_removals(nums) = min_length_after_removals(nums2). Under the preconditions both calls return results.
  Preconditions: Both nums and nums2 satisfy: len >= 1; len <= 100000; all entries in [1,1000000000]; and non-decreasing order (for every i,j with 0 <= i < j < len, value at i <= value at j). -/
theorem spec_12 (nums nums2 : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums))
    (hlen2_pos : 1 ≤ len nums2) (hlen2_le : len nums2 ≤ 100000)
    (hentries2 : EntriesInRange (contents nums2))
    (hsorted2 : Sorted (contents nums2))
    (hne : len nums = len nums2) (hM : maxMult nums = maxMult nums2) :
    ∃ r1 r2 : Std.I64,
      Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r1 ∧
      Aegis.MinLengthAfterRemovals.min_length_after_removals nums2 = ok r2 ∧
      r1.val = r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums))
    (hlen2_pos : 1 ≤ len nums2) (hlen2_le : len nums2 ≤ 100000)
    (hentries2 : EntriesInRange (contents nums2))
    (hsorted2 : Sorted (contents nums2))
    (hne : len nums = len nums2) (hM : maxMult nums = maxMult nums2), ∃ r1 r2 : Std.I64,
      Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r1 ∧
      Aegis.MinLengthAfterRemovals.min_length_after_removals nums2 = ok r2 ∧
      r1.val = r2.val) := by
  sorry

/-- Let n = len(nums) and let M be the maximum multiplicity in nums. Whenever the call returns a result r with r >= 2, the strict-majority condition 2*M > n holds, and every valid sequence of exactly (n - r)/2 removal operations that leaves r elements leaves all remaining elements equal to the unique value v that occurs M times in nums.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)) :
    ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      2 ≤ r.val →
        2 * (maxMult nums : ℤ) > (len nums : ℤ) ∧
        ∃ v : ℤ, cnt nums v = maxMult nums ∧
          (∀ w : ℤ, cnt nums w = maxMult nums → w = v) ∧
          ∀ (k : ℕ) (l' : List ℤ), (len nums : ℤ) - r.val = 2 * (k : ℤ) →
            RemovalSeq k (contents nums) l' → (l'.length : ℤ) = r.val →
            ∀ x ∈ l', x = v := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ len nums) (hlen_le : len nums ≤ 100000)
    (hentries : EntriesInRange (contents nums))
    (hsorted : Sorted (contents nums)), ∀ r : Std.I64, Aegis.MinLengthAfterRemovals.min_length_after_removals nums = ok r →
      2 ≤ r.val →
        2 * (maxMult nums : ℤ) > (len nums : ℤ) ∧
        ∃ v : ℤ, cnt nums v = maxMult nums ∧
          (∀ w : ℤ, cnt nums w = maxMult nums → w = v) ∧
          ∀ (k : ℕ) (l' : List ℤ), (len nums : ℤ) - r.val = 2 * (k : ℤ) →
            RemovalSeq k (contents nums) l' → (l'.length : ℤ) = r.val →
            ∀ x ∈ l', x = v) := by
  sorry

end AegisSpec.MinLengthAfterRemovals
