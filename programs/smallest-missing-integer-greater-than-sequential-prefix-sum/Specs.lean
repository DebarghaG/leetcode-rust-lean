import Aegis.MissingInteger.Code.Funs

/-!
# Specifications of `Aegis.MissingInteger.missing_integer`

LeetCode problem `smallest-missing-integer-greater-than-sequential-prefix-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MissingInteger

  def seqPrefixAux : Int → List Std.I64 → Nat
    | _, [] => 0
    | x, y :: ys => if y.val = x + 1 then 1 + seqPrefixAux y.val ys else 0

  def seqPrefixLen : List Std.I64 → Nat
    | [] => 0
    | x :: xs => 1 + seqPrefixAux x.val xs

  def prefixSum (l : List Std.I64) : Int :=
    ((l.take (seqPrefixLen l)).map (fun x => x.val)).sum

  def Occurs (l : List Std.I64) (v : Int) : Prop :=
    ∃ x, x ∈ l ∧ x.val = v

  def distinctGe (l : List Std.I64) (p : Int) : Nat :=
    (((l.filter (fun x => p ≤ x.val)).map (fun x => x.val)).dedup).length

  def suffixVals (l : List Std.I64) (L : Nat) : List Int :=
    (l.drop (L + 1)).map (fun x => x.val)

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. The function returns a result r and r is the smallest integer satisfying both r >= P and r != nums[i] for every i with 0 <= i < len(nums). Equivalently, r >= P, r is not equal to any nums[i], and for every integer y with P <= y < r there exists i with 0 <= i < len(nums) and nums[i] = y.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∃ r : Std.I64,
        Aegis.MissingInteger.missing_integer nums = ok r ∧
        prefixSum nums.val ≤ r.val ∧
        (∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val) ∧
        (∀ y : Int, prefixSum nums.val ≤ y → y < r.val →
          ∃ i : Fin nums.val.length, (nums.val.get i).val = y) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∃ r : Std.I64,
          Aegis.MissingInteger.missing_integer nums = ok r ∧
          prefixSum nums.val ≤ r.val ∧
          (∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val) ∧
          (∀ y : Int, prefixSum nums.val ≤ y → y < r.val →
            ∃ i : Fin nums.val.length, (nums.val.get i).val = y)) := by
    sorry

  /-- The function returns some 64-bit integer result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∃ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∃ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r) := by
    sorry

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. Whenever the function returns a result r, r >= P.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∀ r : Std.I64,
        Aegis.MissingInteger.missing_integer nums = ok r → prefixSum nums.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∀ r : Std.I64,
          Aegis.MissingInteger.missing_integer nums = ok r → prefixSum nums.val ≤ r.val) := by
    sorry

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. Whenever the function returns a result r, r <= P + len(nums).
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_4 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∀ r : Std.I64,
        Aegis.MissingInteger.missing_integer nums = ok r →
          r.val ≤ prefixSum nums.val + (nums.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∀ r : Std.I64,
          Aegis.MissingInteger.missing_integer nums = ok r →
            r.val ≤ prefixSum nums.val + (nums.val.length : Int)) := by
    sorry

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. Let d be the number of distinct integers v such that v = nums[i] for some i with 0 <= i < len(nums) and v >= P. Whenever the function returns a result r, r <= P + d.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∀ r : Std.I64,
        Aegis.MissingInteger.missing_integer nums = ok r →
          r.val ≤ prefixSum nums.val + (distinctGe nums.val (prefixSum nums.val) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∀ r : Std.I64,
          Aegis.MissingInteger.missing_integer nums = ok r →
            r.val ≤ prefixSum nums.val + (distinctGe nums.val (prefixSum nums.val) : Int)) := by
    sorry

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. Whenever the function returns a result r, for every i with 0 <= i < len(nums), nums[i] != r.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∀ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r →
        ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∀ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r →
          ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val) := by
    sorry

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. Whenever the function returns a result r, for every integer y with P <= y < r, there exists i with 0 <= i < len(nums) and nums[i] = y.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∀ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r →
        ∀ y : Int, prefixSum nums.val ≤ y → y < r.val →
          ∃ i : Fin nums.val.length, (nums.val.get i).val = y := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∀ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r →
          ∀ y : Int, prefixSum nums.val ≤ y → y < r.val →
            ∃ i : Fin nums.val.length, (nums.val.get i).val = y) := by
    sorry

  /-- Let L be the unique integer such that 1 <= L <= len(nums), nums[j] = nums[j-1] + 1 for every j with 1 <= j < L, and if L < len(nums) then nums[L] != nums[L-1] + 1; let P = sum_{j=0}^{L-1} nums[j]. Whenever the function returns a result r, r = P if and only if there is no index i with 0 <= i < len(nums) and nums[i] = P.
    Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50) :
      ∀ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r →
        (r.val = prefixSum nums.val ↔
          ¬ ∃ i : Fin nums.val.length, (nums.val.get i).val = prefixSum nums.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50), ∀ r : Std.I64, Aegis.MissingInteger.missing_integer nums = ok r →
          (r.val = prefixSum nums.val ↔
            ¬ ∃ i : Fin nums.val.length, (nums.val.get i).val = prefixSum nums.val)) := by
    sorry

  /-- Let L be the length of the longest sequential prefix of nums, and suppose L < len(nums). If len(nums2) = len(nums), nums2[i] = nums[i] for every i with 0 <= i <= L, and the multiset of values nums[i] with L < i < len(nums) equals the multiset of values nums2[i] with L < i < len(nums2), then missing_integer(nums) = missing_integer(nums2).
    Preconditions: nums and nums2 are two nonempty slices of 64-bit integers, each satisfying 1 <= length <= 50 and 1 <= element <= 50 for every element. -/
  theorem spec_9 (nums nums2 : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50)
      (hne2 : 1 ≤ nums2.val.length) (hlen2 : nums2.val.length ≤ 50)
      (helem2 : ∀ i : Fin nums2.val.length, 1 ≤ (nums2.val.get i).val ∧ (nums2.val.get i).val ≤ 50)
      (hL : seqPrefixLen nums.val < nums.val.length)
      (hlen12 : nums2.val.length = nums.val.length)
      (hagree : ∀ i : Nat, i ≤ seqPrefixLen nums.val → nums.val[i]? = nums2.val[i]?)
      (hperm : (suffixVals nums.val (seqPrefixLen nums.val)).Perm
        (suffixVals nums2.val (seqPrefixLen nums.val))) :
      ∀ r r2 : Std.I64,
        Aegis.MissingInteger.missing_integer nums = ok r →
        Aegis.MissingInteger.missing_integer nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50)
        (hne2 : 1 ≤ nums2.val.length) (hlen2 : nums2.val.length ≤ 50)
        (helem2 : ∀ i : Fin nums2.val.length, 1 ≤ (nums2.val.get i).val ∧ (nums2.val.get i).val ≤ 50)
        (hL : seqPrefixLen nums.val < nums.val.length)
        (hlen12 : nums2.val.length = nums.val.length)
        (hagree : ∀ i : Nat, i ≤ seqPrefixLen nums.val → nums.val[i]? = nums2.val[i]?)
        (hperm : (suffixVals nums.val (seqPrefixLen nums.val)).Perm
          (suffixVals nums2.val (seqPrefixLen nums.val))), ∀ r r2 : Std.I64,
          Aegis.MissingInteger.missing_integer nums = ok r →
          Aegis.MissingInteger.missing_integer nums2 = ok r2 → r = r2) := by
    sorry

  /-- If P = P2 and for every integer v, v occurs in nums if and only if v occurs in nums2, then whenever the function returns r on nums and r2 on nums2, r = r2.
    Preconditions: nums and nums2 are two nonempty slices of 64-bit integers, each satisfying 1 <= length <= 50 and 1 <= element <= 50 for every element. Let P be the sum of the longest sequential prefix of nums and P2 the sum of the longest sequential prefix of nums2. -/
  theorem spec_10 (nums nums2 : Slice Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
      (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50)
      (hne2 : 1 ≤ nums2.val.length) (hlen2 : nums2.val.length ≤ 50)
      (helem2 : ∀ i : Fin nums2.val.length, 1 ≤ (nums2.val.get i).val ∧ (nums2.val.get i).val ≤ 50)
      (hsum : prefixSum nums.val = prefixSum nums2.val)
      (hocc : ∀ v : Int, Occurs nums.val v ↔ Occurs nums2.val v) :
      ∀ r r2 : Std.I64,
        Aegis.MissingInteger.missing_integer nums = ok r →
        Aegis.MissingInteger.missing_integer nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 50)
        (helem : ∀ i : Fin nums.val.length, 1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 50)
        (hne2 : 1 ≤ nums2.val.length) (hlen2 : nums2.val.length ≤ 50)
        (helem2 : ∀ i : Fin nums2.val.length, 1 ≤ (nums2.val.get i).val ∧ (nums2.val.get i).val ≤ 50)
        (hsum : prefixSum nums.val = prefixSum nums2.val)
        (hocc : ∀ v : Int, Occurs nums.val v ↔ Occurs nums2.val v), ∀ r r2 : Std.I64,
          Aegis.MissingInteger.missing_integer nums = ok r →
          Aegis.MissingInteger.missing_integer nums2 = ok r2 → r = r2) := by
    sorry

  end AegisSpec.MissingInteger
