import Aegis.SumOfEncryptedInt.Code.Funs

/-!
# Specifications of `Aegis.SumOfEncryptedInt.sum_of_encrypted_int`

LeetCode problem `find-the-sum-of-encrypted-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SumOfEncryptedInt

  namespace AegisSpec.SumOfEncryptedInt

  def repunit (d : Nat) : Nat := (10 ^ d - 1) / 9

  def numDigits (x : Int) : Nat := if x ≤ 0 then 0 else Nat.log 10 x.toNat + 1

  def maxDigit (x : Int) : Nat :=
    (List.range (numDigits x)).foldl (fun m k => max m ((x.toNat / 10 ^ k) % 10)) 0

  def enc (x : Int) : Int := ((maxDigit x * repunit (numDigits x) : Nat) : Int)

  def IsIndexPerm (n : Nat) (p : Nat → Nat) : Prop :=
    (∀ i, i < n → p i < n) ∧ ∀ j, j < n → ∃ i, i < n ∧ p i = j

  /-- Whenever the function returns a result r, r = sum_{i=0}^{len(nums)-1} enc(nums[i]), where for a positive integer x, enc(x) is defined as follows: let d be the number of decimal digits in the usual decimal representation of x (no leading zeros) and let m be the largest of those d digits; then enc(x) is the d-digit integer all of whose decimal digits equal m, equivalently enc(x) = m * (10^d - 1) / 9.
    Preconditions: 1 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (r : I64) (hr : sum_of_encrypted_int nums = ok r) :
      r.val = (nums.val.map (fun x => enc x.val)).sum := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (r : I64) (hr : sum_of_encrypted_int nums = ok r), r.val = (nums.val.map (fun x => enc x.val)).sum) := by
    sorry

  /-- Under the preconditions, the function returns some result r; it does not fail by arithmetic overflow, out-of-bounds access, panic, or any other error.
    Preconditions: 1 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000) :
      ∃ r : I64, sum_of_encrypted_int nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000), ∃ r : I64, sum_of_encrypted_int nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(nums) <= r <= 1111 * len(nums).
    Preconditions: 1 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (r : I64) (hr : sum_of_encrypted_int nums = ok r) :
      (nums.val.length : Int) ≤ r.val ∧ r.val ≤ 1111 * (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (r : I64) (hr : sum_of_encrypted_int nums = ok r), (nums.val.length : Int) ≤ r.val ∧ r.val ≤ 1111 * (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r >= sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: 1 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (r : I64) (hr : sum_of_encrypted_int nums = ok r) :
      (nums.val.map (fun x => x.val)).sum ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (r : I64) (hr : sum_of_encrypted_int nums = ok r), (nums.val.map (fun x => x.val)).sum ≤ r.val) := by
    sorry

  /-- Whenever the function returns r on nums and r2 on nums2, r = r2.
    Preconditions: Let L = len(nums). Assume 1 <= L <= 50, every entry of nums and nums2 lies in 1..1000, len(nums2) = L, and there is a permutation p of {0,...,L-1} such that nums2[i] = nums[p(i)] for every i with 0 <= i < L. -/
  theorem spec_5 (nums nums2 : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (hentries2 : ∀ x ∈ nums2.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (hlen2 : nums2.val.length = nums.val.length)
      (hperm : ∃ p : Nat → Nat, IsIndexPerm nums.val.length p ∧
        ∀ (i : Nat), i < nums.val.length → nums2.val[i]? = nums.val[p i]?)
      (r r2 : I64)
      (hr : sum_of_encrypted_int nums = ok r)
      (hr2 : sum_of_encrypted_int nums2 = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (hentries2 : ∀ x ∈ nums2.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (hlen2 : nums2.val.length = nums.val.length)
        (hperm : ∃ p : Nat → Nat, IsIndexPerm nums.val.length p ∧
          ∀ (i : Nat), i < nums.val.length → nums2.val[i]? = nums.val[p i]?)
        (r r2 : I64)
        (hr : sum_of_encrypted_int nums = ok r)
        (hr2 : sum_of_encrypted_int nums2 = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever the function returns ra on a, rb on b, and rc on c, rc = ra + rb.
    Preconditions: a and b are nonempty slices with every entry in 1..1000, and len(a) + len(b) <= 50. Let c be the concatenation of a followed by b. -/
  theorem spec_6 (a b c : Slice I64)
      (ha_nonempty : 0 < a.val.length) (hb_nonempty : 0 < b.val.length)
      (ha_entries : ∀ x ∈ a.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (hb_entries : ∀ x ∈ b.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (hlen : a.val.length + b.val.length ≤ 50)
      (hc : c.val = a.val ++ b.val)
      (ra rb rc : I64)
      (hra : sum_of_encrypted_int a = ok ra)
      (hrb : sum_of_encrypted_int b = ok rb)
      (hrc : sum_of_encrypted_int c = ok rc) :
      rc.val = ra.val + rb.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c : Slice I64)
        (ha_nonempty : 0 < a.val.length) (hb_nonempty : 0 < b.val.length)
        (ha_entries : ∀ x ∈ a.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (hb_entries : ∀ x ∈ b.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (hlen : a.val.length + b.val.length ≤ 50)
        (hc : c.val = a.val ++ b.val)
        (ra rb rc : I64)
        (hra : sum_of_encrypted_int a = ok ra)
        (hrb : sum_of_encrypted_int b = ok rb)
        (hrc : sum_of_encrypted_int c = ok rc), rc.val = ra.val + rb.val) := by
    sorry

  /-- Whenever the function returns a result r, r is divisible by R_d = (10^d - 1) / 9. More exactly, r = R_d * sum_{i=0}^{len(nums)-1} M(nums[i]), where M(x) denotes the largest decimal digit of x.
    Preconditions: 1 <= len(nums) <= 50, every nums[i] lies in 1..1000, and there exists an integer d with 1 <= d <= 4 such that every nums[i] has exactly d decimal digits. -/
  theorem spec_7 (nums : Slice I64) (d : Nat)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (hd_lower : 1 ≤ d) (hd_upper : d ≤ 4)
      (hd : ∀ x ∈ nums.val, numDigits x.val = d)
      (r : I64) (hr : sum_of_encrypted_int nums = ok r) :
      r.val = (repunit d : Int) *
        (nums.val.map (fun x => ((maxDigit x.val : Nat) : Int))).sum := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (d : Nat)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (hd_lower : 1 ≤ d) (hd_upper : d ≤ 4)
        (hd : ∀ x ∈ nums.val, numDigits x.val = d)
        (r : I64) (hr : sum_of_encrypted_int nums = ok r), r.val = (repunit d : Int) *
          (nums.val.map (fun x => ((maxDigit x.val : Nat) : Int))).sum) := by
    sorry

  /-- Whenever the function returns r on nums and r2 on nums2, r2 = r.
    Preconditions: 1 <= len(nums) <= 50, every nums[i] lies in 1..999, and nums2 is a slice of length len(nums) such that nums2[i] = enc(nums[i]) for every i, where enc(x) replaces every decimal digit of x by the largest decimal digit of x. -/
  theorem spec_8 (nums nums2 : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 999)
      (hlen2 : nums2.val.length = nums.val.length)
      (h2 : nums2.val.map (fun x => x.val) = nums.val.map (fun x => enc x.val))
      (r r2 : I64)
      (hr : sum_of_encrypted_int nums = ok r)
      (hr2 : sum_of_encrypted_int nums2 = ok r2) :
      r2.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 999)
        (hlen2 : nums2.val.length = nums.val.length)
        (h2 : nums2.val.map (fun x => x.val) = nums.val.map (fun x => enc x.val))
        (r r2 : I64)
        (hr : sum_of_encrypted_int nums = ok r)
        (hr2 : sum_of_encrypted_int nums2 = ok r2), r2.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 999 * len(nums).
    Preconditions: 1 <= len(nums) <= 50 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 999. -/
  theorem spec_9 (nums : Slice I64)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 999)
      (r : I64) (hr : sum_of_encrypted_int nums = ok r) :
      r.val ≤ 999 * (nums.val.length : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 999)
        (r : I64) (hr : sum_of_encrypted_int nums = ok r), r.val ≤ 999 * (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = m * sum_{i=0}^{len(nums)-1} ((10^{d_i} - 1) / 9), where d_i is the number of decimal digits of nums[i].
    Preconditions: 1 <= len(nums) <= 50, every nums[i] lies in 1..1000, and there exists an integer m with 1 <= m <= 9 such that for every i, the largest decimal digit of nums[i] is m. -/
  theorem spec_10 (nums : Slice I64) (m : Nat)
      (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
      (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
      (hm_lower : 1 ≤ m) (hm_upper : m ≤ 9)
      (hm : ∀ x ∈ nums.val, maxDigit x.val = m)
      (r : I64) (hr : sum_of_encrypted_int nums = ok r) :
      r.val = (m : Int) *
        (nums.val.map (fun x => (repunit (numDigits x.val) : Int))).sum := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (m : Nat)
        (hlen_nonempty : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50)
        (hentries : ∀ x ∈ nums.val, (1 : Int) ≤ x.val ∧ x.val ≤ 1000)
        (hm_lower : 1 ≤ m) (hm_upper : m ≤ 9)
        (hm : ∀ x ∈ nums.val, maxDigit x.val = m)
        (r : I64) (hr : sum_of_encrypted_int nums = ok r), r.val = (m : Int) *
          (nums.val.map (fun x => (repunit (numDigits x.val) : Int))).sum) := by
    sorry

  end AegisSpec.SumOfEncryptedInt
