import Aegis.LargestEvenSum.Code.Funs

/-!
# Specifications of `Aegis.LargestEvenSum.largest_even_sum`

LeetCode problem `subsequence-of-size-k-with-the-largest-even-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargestEvenSum

  def IsSubseqIndex (nums : Slice Std.I64) (k : Nat)
      (f : Fin k → Fin nums.val.length) : Prop :=
    ∀ i j : Fin k, i < j → f i < f j

  def subseqSum (nums : Slice Std.I64) (k : Nat)
      (f : Fin k → Fin nums.val.length) : Int :=
    ∑ i : Fin k, (nums.val.get (f i)).val

  def HasSubseqSumOfLen (nums : Slice Std.I64) (k : Nat) (s : Int) : Prop :=
    ∃ f : Fin k → Fin nums.val.length, IsSubseqIndex nums k f ∧ subseqSum nums k f = s

  def SameMultisetOfEntries (nums nums' : Slice Std.I64) : Prop :=
    ∀ v : Int,
      (nums.val.filter (fun x => x.val = v)).length =
        (nums'.val.filter (fun x => x.val = v)).length

  /-- Define a length-k subsequence of nums to be a choice of indices i_0, ..., i_{k-1} with 0 <= i_0 < ... < i_{k-1} < len(nums), whose sum is nums[i_0] + ... + nums[i_{k-1}]. Whenever largest_even_sum nums k returns a result r, either: (1) r = -1 and there is no length-k subsequence of nums whose sum is even; or (2) r is even, there is a length-k subsequence of nums whose sum is r, and for every length-k subsequence of nums with sum s, if s is even then s <= r.
    Preconditions: 1 <= len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
      (hentries : ∀ (i : Nat) (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000) :
      ∀ r : Std.I64,
        Aegis.LargestEvenSum.largest_even_sum nums k = ok r →
        (r.val = -1 ∧
            ¬ ∃ s : Int, HasSubseqSumOfLen nums k.val.toNat s ∧ Even s) ∨
          (Even r.val ∧ HasSubseqSumOfLen nums k.val.toNat r.val ∧
            ∀ s : Int, HasSubseqSumOfLen nums k.val.toNat s → Even s → s ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
        (hentries : ∀ (i : Nat) (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000), ∀ r : Std.I64,
          Aegis.LargestEvenSum.largest_even_sum nums k = ok r →
          (r.val = -1 ∧
              ¬ ∃ s : Int, HasSubseqSumOfLen nums k.val.toNat s ∧ Even s) ∨
            (Even r.val ∧ HasSubseqSumOfLen nums k.val.toNat r.val ∧
              ∀ s : Int, HasSubseqSumOfLen nums k.val.toNat s → Even s → s ≤ r.val)) := by
    sorry

  /-- For every nums and k satisfying the preconditions, largest_even_sum nums k returns a result r (it does not fail, panic, go out of bounds, or encounter arithmetic overflow).
    Preconditions: 1 <= len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
      (hentries : ∀ (i : Nat) (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000) :
      ∃ r : Std.I64, Aegis.LargestEvenSum.largest_even_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
        (hentries : ∀ (i : Nat) (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000), ∃ r : Std.I64, Aegis.LargestEvenSum.largest_even_sum nums k = ok r) := by
    sorry

  /-- Whenever largest_even_sum nums k returns r and largest_even_sum nums' k returns r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums' is a slice with len(nums') = len(nums) and, for every integer value v, the number of indices i with nums[i] = v equals the number of indices j with nums'[j] = v. -/
  theorem spec_3 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
      (hentries : ∀ (i : Nat) (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hlen'_eq : nums'.val.length = nums.val.length)
      (hmult : SameMultisetOfEntries nums nums') :
      ∀ r r' : Std.I64,
        Aegis.LargestEvenSum.largest_even_sum nums k = ok r →
        Aegis.LargestEvenSum.largest_even_sum nums' k = ok r' → r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
        (hentries : ∀ (i : Nat) (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hlen'_eq : nums'.val.length = nums.val.length)
        (hmult : SameMultisetOfEntries nums nums'), ∀ r r' : Std.I64,
          Aegis.LargestEvenSum.largest_even_sum nums k = ok r →
          Aegis.LargestEvenSum.largest_even_sum nums' k = ok r' → r = r') := by
    sorry

  /-- Whenever largest_even_sum nums k returns r and largest_even_sum nums' k returns r', then r = -1 if and only if r' = -1; moreover, if r != -1 then r' = r + k*c.
    Preconditions: 1 <= len(nums) <= 100000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; c is an even integer; nums' is a slice with len(nums') = len(nums) and nums'[i] = nums[i] + c for every i with 0 <= i < len(nums); and nums' also satisfies the same problem constraints (length 1..100000, entries 0..100000, and k <= len(nums')). -/
  theorem spec_4 (nums nums' : Slice Std.I64) (k : Std.I64) (c : Int)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
      (hentries : ∀ (i : Nat) (h : i < nums.val.length),
        0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
      (hc : Even c)
      (hlen'_eq : nums'.val.length = nums.val.length)
      (hshift : ∀ (i : Nat) (h : i < nums.val.length),
        (nums'.val[i]'(hlen'_eq ▸ h)).val = (nums.val[i]'h).val + c)
      (hlen'_lo : 1 ≤ nums'.val.length) (hlen'_hi : nums'.val.length ≤ 100000)
      (hk'_hi : k.val ≤ (nums'.val.length : Int))
      (hentries' : ∀ (i : Nat) (h : i < nums'.val.length),
        0 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 100000) :
      ∀ r r' : Std.I64,
        Aegis.LargestEvenSum.largest_even_sum nums k = ok r →
        Aegis.LargestEvenSum.largest_even_sum nums' k = ok r' →
        (r.val = -1 ↔ r'.val = -1) ∧
          (r.val ≠ -1 → r'.val = r.val + k.val * c) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (c : Int)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : Int))
        (hentries : ∀ (i : Nat) (h : i < nums.val.length),
          0 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100000)
        (hc : Even c)
        (hlen'_eq : nums'.val.length = nums.val.length)
        (hshift : ∀ (i : Nat) (h : i < nums.val.length),
          (nums'.val[i]'(hlen'_eq ▸ h)).val = (nums.val[i]'h).val + c)
        (hlen'_lo : 1 ≤ nums'.val.length) (hlen'_hi : nums'.val.length ≤ 100000)
        (hk'_hi : k.val ≤ (nums'.val.length : Int))
        (hentries' : ∀ (i : Nat) (h : i < nums'.val.length),
          0 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 100000), ∀ r r' : Std.I64,
          Aegis.LargestEvenSum.largest_even_sum nums k = ok r →
          Aegis.LargestEvenSum.largest_even_sum nums' k = ok r' →
          (r.val = -1 ↔ r'.val = -1) ∧
            (r.val ≠ -1 → r'.val = r.val + k.val * c)) := by
    sorry

  end AegisSpec.LargestEvenSum
