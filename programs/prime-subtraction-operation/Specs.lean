import Aegis.PrimeSubOperation.Code.Funs

/-!
# Specifications of `Aegis.PrimeSubOperation.prime_sub_operation`

LeetCode problem `prime-subtraction-operation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.PrimeSubOperation

  namespace AegisSpec.PrimeSubOperation

  def IsPrimeInt (z : ℤ) : Prop := ∃ p : ℕ, Nat.Prime p ∧ z = (p : ℤ)

  def numsGet (nums : Slice I64) (n : ℕ) (hn : nums.val.length = n) (i : ℕ) (hi : i < n) : ℤ :=
    (nums.val.get ⟨i, by omega⟩).val

  def arrGet (b : List ℤ) (n : ℕ) (hb : b.length = n) (i : ℕ) (hi : i < n) : ℤ :=
    b.get ⟨i, by omega⟩

  def Bounded (nums : Slice I64) (n : ℕ) (hn : nums.val.length = n) (lo hi : ℤ) : Prop :=
    ∀ (i : ℕ) (hi' : i < n), lo ≤ numsGet nums n hn i hi' ∧ numsGet nums n hn i hi' ≤ hi

  def Admissible (nums : Slice I64) (n : ℕ) (hn : nums.val.length = n) (b : List ℤ)
      (hb : b.length = n) : Prop :=
    ∀ (i : ℕ) (hi : i < n),
      arrGet b n hb i hi = numsGet nums n hn i hi ∨
        (1 ≤ arrGet b n hb i hi ∧ arrGet b n hb i hi < numsGet nums n hn i hi ∧
          IsPrimeInt (numsGet nums n hn i hi - arrGet b n hb i hi))

  def StrictInc (b : List ℤ) (n : ℕ) (hb : b.length = n) : Prop :=
    ∀ (i : ℕ) (hi : i + 1 < n), arrGet b n hb i (by omega) < arrGet b n hb (i + 1) (by omega)

  def NumsStrictInc (nums : Slice I64) (n : ℕ) (hn : nums.val.length = n) : Prop :=
    ∀ (i : ℕ) (hi : i + 1 < n),
      numsGet nums n hn i (by omega) < numsGet nums n hn (i + 1) (by omega)

  lemma val_length_eq_leng (nums : Slice I64) : nums.val.length = nums.leng :=
    Aeneas.Data.ListN.ListN_length nums.list

  lemma val_length_le_max (nums : Slice I64) : nums.val.length ≤ Aeneas.Std.Usize.max := by
    have h := nums.bound
    have h' := val_length_eq_leng nums
    omega

  lemma thousand_le_usizeMax : (1000 : ℕ) ≤ Aeneas.Std.Usize.max := by
    have hmax : Aeneas.Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
      simp [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits]
    rw [hmax]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num

  def subSlice (nums : Slice I64) (l r : ℕ) : Slice I64 :=
    Slice.from (nums.val.slice l (r + 1)) (by
      have h1 : (nums.val.slice l (r + 1)).length ≤ nums.val.length := by
        simp only [List.slice, List.length_take, List.length_drop]
        omega
      have h2 := val_length_le_max nums
      omega)

  def pushBack (nums : Slice I64) (n : ℕ) (hn : nums.val.length = n) (hn_le : n ≤ 999)
      (x : I64) : Slice I64 :=
    Slice.from (nums.val ++ [x]) (by
      have h1 : (nums.val ++ [x]).length = nums.val.length + 1 := by simp
      have h2 := thousand_le_usizeMax
      omega)

  lemma subSlice_val (nums : Slice I64) (l r : ℕ) :
      (subSlice nums l r).val = nums.val.slice l (r + 1) := by
    simp [subSlice, Slice.from, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  lemma pushBack_val (nums : Slice I64) (n : ℕ) (hn : nums.val.length = n) (hn_le : n ≤ 999)
      (x : I64) : (pushBack nums n hn hn_le x).val = nums.val ++ [x] := by
    simp [pushBack, Slice.from, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  /-- Whenever prime_sub_operation nums returns a result r, r = true if and only if there exists an integer array b of length n such that: (1) for every i with 0 <= i < n, either b[i] = nums[i], or (1 <= b[i] < nums[i] and nums[i] - b[i] is a prime number); (2) for every i with 0 <= i < n-1, b[i] < b[i+1] (equivalently b[0] < b[1] < ... < b[n-1]).
    Preconditions: Let n = len(nums). 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 1000) :
      ∀ (r : Bool), prime_sub_operation nums = Result.ok r →
        (r = true ↔ ∃ (b : List ℤ) (hb : b.length = n),
          Admissible nums n hn b hb ∧ StrictInc b n hb) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 1000), ∀ (r : Bool), prime_sub_operation nums = Result.ok r →
          (r = true ↔ ∃ (b : List ℤ) (hb : b.length = n),
            Admissible nums n hn b hb ∧ StrictInc b n hb)) := by
    sorry

  /-- There exists a Boolean r such that prime_sub_operation nums = Result.ok r; thus the function does not fail by panic, overflow, or out-of-bounds access on these inputs.
    Preconditions: Let n = len(nums). 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 1000) :
      ∃ r : Bool, prime_sub_operation nums = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 1000), ∃ r : Bool, prime_sub_operation nums = Result.ok r) := by
    sorry

  /-- Whenever prime_sub_operation nums returns a result r, r = false.
    Preconditions: Let n = len(nums). 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums[i] <= 1000, and there exists i with 0 <= i < n and nums[i] <= i. -/
  theorem spec_3 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 1000)
      (hwitness : ∃ (i : ℕ) (hi : i < n), numsGet nums n hn i hi ≤ (i : ℤ)) :
      ∀ (r : Bool), prime_sub_operation nums = Result.ok r → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 1000)
        (hwitness : ∃ (i : ℕ) (hi : i < n), numsGet nums n hn i hi ≤ (i : ℤ)), ∀ (r : Bool), prime_sub_operation nums = Result.ok r → r = false) := by
    sorry

  /-- Whenever prime_sub_operation nums returns a result r, r = true if and only if nums[0] < nums[1] < ... < nums[n-1].
    Preconditions: Let n = len(nums). 2 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 2. -/
  theorem spec_4 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_ge : 2 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 2) :
      ∀ (r : Bool), prime_sub_operation nums = Result.ok r →
        (r = true ↔ NumsStrictInc nums n hn) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_ge : 2 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 2), ∀ (r : Bool), prime_sub_operation nums = Result.ok r →
          (r = true ↔ NumsStrictInc nums n hn)) := by
    sorry

  /-- If prime_sub_operation nums returns true, then there exists an integer array b of length n such that: (1) for every i with 0 <= i < n, either b[i] = nums[i], or (1 <= b[i] < nums[i] and nums[i] - b[i] is a prime number); (2) b[0] < b[1] < ... < b[n-1]; (3) b[n-1] = nums[n-1].
    Preconditions: Let n = len(nums). 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 1000) :
      ∀ (r : Bool), prime_sub_operation nums = Result.ok r → r = true →
        ∃ (b : List ℤ) (hb : b.length = n),
          Admissible nums n hn b hb ∧ StrictInc b n hb ∧
            arrGet b n hb (n - 1) (by omega) = numsGet nums n hn (n - 1) (by omega) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 1000), ∀ (r : Bool), prime_sub_operation nums = Result.ok r → r = true →
          ∃ (b : List ℤ) (hb : b.length = n),
            Admissible nums n hn b hb ∧ StrictInc b n hb ∧
              arrGet b n hb (n - 1) (by omega) = numsGet nums n hn (n - 1) (by omega)) := by
    sorry

  /-- Whenever prime_sub_operation nums returns a result r, r = true if and only if for every i with 0 <= i < n, either nums[i] = i+1, or (i+1 < nums[i] and nums[i] - (i+1) is a prime number).
    Preconditions: Let n = len(nums). 2 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums[i] <= 1000, and nums[n-1] = n. -/
  theorem spec_6 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_ge : 2 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 1000)
      (hlast : numsGet nums n hn (n - 1) (by omega) = (n : ℤ)) :
      ∀ (r : Bool), prime_sub_operation nums = Result.ok r →
        (r = true ↔ ∀ (i : ℕ) (hi : i < n),
          numsGet nums n hn i hi = (i : ℤ) + 1 ∨
            ((i : ℤ) + 1 < numsGet nums n hn i hi ∧
              IsPrimeInt (numsGet nums n hn i hi - ((i : ℤ) + 1)))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_ge : 2 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 1000)
        (hlast : numsGet nums n hn (n - 1) (by omega) = (n : ℤ)), ∀ (r : Bool), prime_sub_operation nums = Result.ok r →
          (r = true ↔ ∀ (i : ℕ) (hi : i < n),
            numsGet nums n hn i hi = (i : ℤ) + 1 ∨
              ((i : ℤ) + 1 < numsGet nums n hn i hi ∧
                IsPrimeInt (numsGet nums n hn i hi - ((i : ℤ) + 1))))) := by
    sorry

  /-- If prime_sub_operation nums returns true, then for every l and r with 0 <= l <= r < n, prime_sub_operation on the slice nums[l], nums[l+1], ..., nums[r] returns true.
    Preconditions: Let n = len(nums). 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_7 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hbounds : Bounded nums n hn 1 1000) :
      ∀ (r : Bool), prime_sub_operation nums = Result.ok r → r = true →
        ∀ (l r' : ℕ), l ≤ r' → r' < n →
          prime_sub_operation (subSlice nums l r') = Result.ok true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hbounds : Bounded nums n hn 1 1000), ∀ (r : Bool), prime_sub_operation nums = Result.ok r → r = true →
          ∀ (l r' : ℕ), l ≤ r' → r' < n →
            prime_sub_operation (subSlice nums l r') = Result.ok true) := by
    sorry

  /-- prime_sub_operation on nums2 returns true.
    Preconditions: Let n = len(nums). 1 <= n <= 999, for every i with 0 <= i < n, 1 <= nums[i] <= 1000, prime_sub_operation nums returns true, and x is an integer with 1 <= x <= 1000 and nums[n-1] < x. Let nums2 be the length n+1 array with nums2[i] = nums[i] for 0 <= i < n and nums2[n] = x. -/
  theorem spec_8 (nums : Slice I64) (n : ℕ)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 999)
      (hbounds : Bounded nums n hn 1 1000)
      (hok : prime_sub_operation nums = Result.ok true)
      (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 1000)
      (hx_gt : numsGet nums n hn (n - 1) (by omega) < x.val) :
      prime_sub_operation (pushBack nums n hn hn_le x) = Result.ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (n : ℕ)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 999)
        (hbounds : Bounded nums n hn 1 1000)
        (hok : prime_sub_operation nums = Result.ok true)
        (x : I64) (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 1000)
        (hx_gt : numsGet nums n hn (n - 1) (by omega) < x.val), prime_sub_operation (pushBack nums n hn hn_le x) = Result.ok true) := by
    sorry

  end AegisSpec.PrimeSubOperation
