import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-maximize-last-elements-in-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinOperations (min_operations)

namespace AegisSpec.MinOperations

def len (s : Slice Std.I64) : Nat := s.val.length

def elem (s : Slice Std.I64) (i : Nat) : Int := (s.val.map (fun v => v.val)).getD i 0

def swappedFst (nums1 nums2 : Slice Std.I64) (S : Finset Nat) (i : Nat) : Int :=
  if i ∈ S then elem nums2 i else elem nums1 i

def swappedSnd (nums1 nums2 : Slice Std.I64) (S : Finset Nat) (i : Nat) : Int :=
  if i ∈ S then elem nums1 i else elem nums2 i

def ValidSwaps (nums1 nums2 : Slice Std.I64) (S : Finset Nat) : Prop :=
  S ⊆ Finset.range (len nums1) ∧
    (∀ i, i < len nums1 → swappedFst nums1 nums2 S i ≤ swappedFst nums1 nums2 S (len nums1 - 1)) ∧
    (∀ i, i < len nums1 → swappedSnd nums1 nums2 S i ≤ swappedSnd nums1 nums2 S (len nums1 - 1))

def LastIsMax (nums1 nums2 : Slice Std.I64) : Prop :=
  (∀ i, i < len nums1 → elem nums1 i ≤ elem nums1 (len nums1 - 1)) ∧
    (∀ i, i < len nums2 → elem nums2 i ≤ elem nums2 (len nums2 - 1))

def lim1 (nums1 nums2 : Slice Std.I64) (b : Nat) : Int :=
  if b = 0 then elem nums1 (len nums1 - 1) else elem nums2 (len nums1 - 1)

def lim2 (nums1 nums2 : Slice Std.I64) (b : Nat) : Int :=
  if b = 0 then elem nums2 (len nums1 - 1) else elem nums1 (len nums1 - 1)

def KeepOk (nums1 nums2 : Slice Std.I64) (b i : Nat) : Prop :=
  elem nums1 i ≤ lim1 nums1 nums2 b ∧ elem nums2 i ≤ lim2 nums1 nums2 b

def SwapOk (nums1 nums2 : Slice Std.I64) (b i : Nat) : Prop :=
  elem nums2 i ≤ lim1 nums1 nums2 b ∧ elem nums1 i ≤ lim2 nums1 nums2 b

def Feasible (nums1 nums2 : Slice Std.I64) (b : Nat) : Prop :=
  b ≤ 1 ∧ ∀ i, i < len nums1 - 1 → KeepOk nums1 nums2 b i ∨ SwapOk nums1 nums2 b i

noncomputable def cost (nums1 nums2 : Slice Std.I64) (b : Nat) : Int := by
  classical
  exact (b : Int) +
    (((Finset.range (len nums1 - 1)).filter (fun i => ¬ KeepOk nums1 nums2 b i)).card : Int)

/-- Let n = len(nums1). The function returns a result r and the following holds. For a set S of indices with S subset of {0,...,n-1}, call S valid if, after swapping nums1[i] with nums2[i] exactly for i in S and leaving all other entries unchanged, the resulting arrays A1 and A2 satisfy A1[i] <= A1[n-1] for every i with 0 <= i < n and A2[i] <= A2[n-1] for every i with 0 <= i < n. Then: if no valid S exists, r = -1; if at least one valid S exists, r != -1, there exists a valid S with |S| = r, and every valid S has |S| >= r. Thus, when feasible, r is the minimum number of swaps needed to make nums1[n-1] the maximum of its array and nums2[n-1] the maximum of its array, and r is -1 exactly when this is impossible.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ r : Std.I64, min_operations nums1 nums2 = ok r ∧
      (r.val = -1 ↔ ¬ ∃ S : Finset Nat, ValidSwaps nums1 nums2 S) ∧
      ((∃ S : Finset Nat, ValidSwaps nums1 nums2 S) →
        (∃ S : Finset Nat, ValidSwaps nums1 nums2 S ∧ (S.card : Int) = r.val) ∧
          (∀ S : Finset Nat, ValidSwaps nums1 nums2 S → r.val ≤ (S.card : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ r : Std.I64, min_operations nums1 nums2 = ok r ∧
      (r.val = -1 ↔ ¬ ∃ S : Finset Nat, ValidSwaps nums1 nums2 S) ∧
      ((∃ S : Finset Nat, ValidSwaps nums1 nums2 S) →
        (∃ S : Finset Nat, ValidSwaps nums1 nums2 S ∧ (S.card : Int) = r.val) ∧
          (∀ S : Finset Nat, ValidSwaps nums1 nums2 S → r.val ≤ (S.card : Int)))) := by
  sorry

/-- The function returns a result r; it does not fail for any input satisfying the preconditions.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ r : Std.I64, min_operations nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ r : Std.I64, min_operations nums1 nums2 = ok r) := by
  sorry

/-- Let n = len(nums1). Whenever the function returns a result r, either r = -1 or 0 <= r <= n - 1. In particular, a feasible answer never requires swapping all n indices.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ r : Std.I64, min_operations nums1 nums2 = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (len nums1 : Int) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ r : Std.I64, min_operations nums1 nums2 = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (len nums1 : Int) - 1)) := by
  sorry

/-- If len(nums1) = 1, then the function returns r = 0.
  Preconditions: len(nums1) = len(nums2) = 1, and 1 <= nums1[0] <= 10^9 and 1 <= nums2[0] <= 10^9. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (h1 : len nums1 = 1) (h2 : len nums2 = 1)
    (hb1 : 1 ≤ elem nums1 0 ∧ elem nums1 0 ≤ 10 ^ 9)
    (hb2 : 1 ≤ elem nums2 0 ∧ elem nums2 0 ≤ 10 ^ 9) :
    ∃ r : Std.I64, min_operations nums1 nums2 = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : len nums1 = 1) (h2 : len nums2 = 1)
    (hb1 : 1 ≤ elem nums1 0 ∧ elem nums1 0 ≤ 10 ^ 9)
    (hb2 : 1 ≤ elem nums2 0 ∧ elem nums2 0 ≤ 10 ^ 9), ∃ r : Std.I64, min_operations nums1 nums2 = ok r ∧ r.val = 0) := by
  sorry

/-- Let n = len(nums1). Whenever the function returns a result r, r = 0 if and only if both of the following hold: nums1[n-1] >= nums1[i] for every i with 0 <= i < n, and nums2[n-1] >= nums2[i] for every i with 0 <= i < n.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ r : Std.I64, min_operations nums1 nums2 = ok r → (r.val = 0 ↔ LastIsMax nums1 nums2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ r : Std.I64, min_operations nums1 nums2 = ok r → (r.val = 0 ↔ LastIsMax nums1 nums2)) := by
  sorry

/-- Let n = len(nums1). Whenever the function returns a result r, r = 1 if and only if: (i) it is not the case that both nums1[n-1] >= nums1[i] for every i with 0 <= i < n and nums2[n-1] >= nums2[i] for every i with 0 <= i < n; and (ii) there exists an index j with 0 <= j < n such that after swapping nums1[j] and nums2[j] and no other entries, the resulting arrays B1 and B2 satisfy B1[i] <= B1[n-1] for every i with 0 <= i < n and B2[i] <= B2[n-1] for every i with 0 <= i < n.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ r : Std.I64, min_operations nums1 nums2 = ok r →
      (r.val = 1 ↔ ¬ LastIsMax nums1 nums2 ∧
        ∃ j, j < len nums1 ∧ ValidSwaps nums1 nums2 {j}) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ r : Std.I64, min_operations nums1 nums2 = ok r →
      (r.val = 1 ↔ ¬ LastIsMax nums1 nums2 ∧
        ∃ j, j < len nums1 ∧ ValidSwaps nums1 nums2 {j})) := by
  sorry

/-- Let r be the result returned for the input pair (nums1, nums2), and let r' be the result returned for the exchanged input pair (nums2, nums1). Then r = r'; that is, the answer is unchanged when the two input arrays are exchanged.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ r r' : Std.I64, min_operations nums1 nums2 = ok r →
      min_operations nums2 nums1 = ok r' → r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ r r' : Std.I64, min_operations nums1 nums2 = ok r →
      min_operations nums2 nums1 = ok r' → r.val = r'.val) := by
  sorry

/-- Let pi be any permutation of {0,...,n-2}. Define arrays nums1' and nums2' of length n by nums1'[i] = nums1[pi(i)] and nums2'[i] = nums2[pi(i)] for 0 <= i < n-1, and nums1'[n-1] = nums1[n-1], nums2'[n-1] = nums2[n-1]. Then the result returned on (nums1', nums2') equals the result returned on (nums1, nums2).
  Preconditions: len(nums1) = len(nums2) = n, n >= 2, 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_8 (n : Nat) (hn : 2 ≤ n) (hcap : n ≤ 1000)
    (nums1 nums2 nums1' nums2' : Slice Std.I64)
    (h1 : len nums1 = n) (h2 : len nums2 = n)
    (h1' : len nums1' = n) (h2' : len nums2' = n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (hb1' : ∀ i, i < n → 1 ≤ elem nums1' i ∧ elem nums1' i ≤ 10 ^ 9)
    (hb2' : ∀ i, i < n → 1 ≤ elem nums2' i ∧ elem nums2' i ≤ 10 ^ 9)
    (pi : Equiv.Perm (Fin (n - 1)))
    (hd1 : ∀ i : Fin (n - 1), elem nums1' i.val = elem nums1 (pi i).val)
    (hd2 : ∀ i : Fin (n - 1), elem nums2' i.val = elem nums2 (pi i).val)
    (hlast1 : elem nums1' (n - 1) = elem nums1 (n - 1))
    (hlast2 : elem nums2' (n - 1) = elem nums2 (n - 1)) :
    ∀ r r' : Std.I64, min_operations nums1 nums2 = ok r →
      min_operations nums1' nums2' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Nat) (hn : 2 ≤ n) (hcap : n ≤ 1000)
    (nums1 nums2 nums1' nums2' : Slice Std.I64)
    (h1 : len nums1 = n) (h2 : len nums2 = n)
    (h1' : len nums1' = n) (h2' : len nums2' = n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (hb1' : ∀ i, i < n → 1 ≤ elem nums1' i ∧ elem nums1' i ≤ 10 ^ 9)
    (hb2' : ∀ i, i < n → 1 ≤ elem nums2' i ∧ elem nums2' i ≤ 10 ^ 9)
    (pi : Equiv.Perm (Fin (n - 1)))
    (hd1 : ∀ i : Fin (n - 1), elem nums1' i.val = elem nums1 (pi i).val)
    (hd2 : ∀ i : Fin (n - 1), elem nums2' i.val = elem nums2 (pi i).val)
    (hlast1 : elem nums1' (n - 1) = elem nums1 (n - 1))
    (hlast2 : elem nums2' (n - 1) = elem nums2 (n - 1)), ∀ r r' : Std.I64, min_operations nums1 nums2 = ok r →
      min_operations nums1' nums2' = ok r' → r.val = r'.val) := by
  sorry

/-- Let f be any strictly increasing function from integers to integers. Define nums1'[i] = f(nums1[i]) and nums2'[i] = f(nums2[i]) for every i with 0 <= i < len(nums1). If every entry of nums1' and nums2' is in the range 1 <= value <= 10^9, then the result returned on (nums1', nums2') equals the result returned on (nums1, nums2).
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_9 (nums1 nums2 nums1' nums2' : Slice Std.I64) (f : Int → Int)
    (hf : ∀ a b : Int, a < b → f a < f b)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (hlen1' : len nums1' = len nums1) (hlen2' : len nums2' = len nums2)
    (hmap1 : ∀ i, i < len nums1 → elem nums1' i = f (elem nums1 i))
    (hmap2 : ∀ i, i < len nums2 → elem nums2' i = f (elem nums2 i))
    (hrange1 : ∀ i, i < len nums1' → 1 ≤ elem nums1' i ∧ elem nums1' i ≤ 10 ^ 9)
    (hrange2 : ∀ i, i < len nums2' → 1 ≤ elem nums2' i ∧ elem nums2' i ≤ 10 ^ 9) :
    ∀ r r' : Std.I64, min_operations nums1 nums2 = ok r →
      min_operations nums1' nums2' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (f : Int → Int)
    (hf : ∀ a b : Int, a < b → f a < f b)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (hlen1' : len nums1' = len nums1) (hlen2' : len nums2' = len nums2)
    (hmap1 : ∀ i, i < len nums1 → elem nums1' i = f (elem nums1 i))
    (hmap2 : ∀ i, i < len nums2 → elem nums2' i = f (elem nums2 i))
    (hrange1 : ∀ i, i < len nums1' → 1 ≤ elem nums1' i ∧ elem nums1' i ≤ 10 ^ 9)
    (hrange2 : ∀ i, i < len nums2' → 1 ≤ elem nums2' i ∧ elem nums2' i ≤ 10 ^ 9), ∀ r r' : Std.I64, min_operations nums1 nums2 = ok r →
      min_operations nums1' nums2' = ok r' → r.val = r'.val) := by
  sorry

/-- Let n = len(nums1). For b in {0,1}, define L1(b) = nums1[n-1] if b = 0 and nums2[n-1] if b = 1, and L2(b) = nums2[n-1] if b = 0 and nums1[n-1] if b = 1. Call b feasible if for every i with 0 <= i < n-1, either (nums1[i] <= L1(b) and nums2[i] <= L2(b)) or (nums2[i] <= L1(b) and nums1[i] <= L2(b)). For feasible b, define cost(b) = b + |{ i : 0 <= i < n-1 and not (nums1[i] <= L1(b) and nums2[i] <= L2(b)) }|. Then the function returns -1 if neither b = 0 nor b = 1 is feasible, and otherwise returns the minimum of cost(b) over feasible b in {0,1}.
  Preconditions: len(nums1) = len(nums2), 1 <= len(nums1) <= 1000, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ r : Std.I64, min_operations nums1 nums2 = ok r ∧
      ((¬ Feasible nums1 nums2 0 ∧ ¬ Feasible nums1 nums2 1) → r.val = -1) ∧
      (∀ b, b ≤ 1 → Feasible nums1 nums2 b → r.val ≤ cost nums1 nums2 b) ∧
      ((Feasible nums1 nums2 0 ∨ Feasible nums1 nums2 1) →
        ∃ b, b ≤ 1 ∧ Feasible nums1 nums2 b ∧ r.val = cost nums1 nums2 b) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen : len nums1 = len nums2) (hpos : 1 ≤ len nums1) (hcap : len nums1 ≤ 1000)
    (hb1 : ∀ i, i < len nums1 → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < len nums1 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ r : Std.I64, min_operations nums1 nums2 = ok r ∧
      ((¬ Feasible nums1 nums2 0 ∧ ¬ Feasible nums1 nums2 1) → r.val = -1) ∧
      (∀ b, b ≤ 1 → Feasible nums1 nums2 b → r.val ≤ cost nums1 nums2 b) ∧
      ((Feasible nums1 nums2 0 ∨ Feasible nums1 nums2 1) →
        ∃ b, b ≤ 1 ∧ Feasible nums1 nums2 b ∧ r.val = cost nums1 nums2 b)) := by
  sorry

end AegisSpec.MinOperations
