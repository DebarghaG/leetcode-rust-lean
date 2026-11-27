import Aegis.MaximizeSum.Code.Funs

/-!
# Specifications of `Aegis.MaximizeSum.maximize_sum`

LeetCode problem `maximum-sum-with-exactly-k-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximizeSum

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def IsMax (l : List Int) (M : Int) : Prop :=
    (∃ (p : Nat) (hp : p < l.length), l.get ⟨p, hp⟩ = M) ∧
      ∀ (i : Nat) (hi : i < l.length), l.get ⟨i, hi⟩ ≤ M

  def IsSliceMax (nums : Slice Std.I64) (M : Int) : Prop := IsMax (contents nums) M

  /-- The function returns a result r and r = k*M + (k*(k-1))/2, where M is the maximum value in nums: there exists p with 0 <= p < len(nums) such that nums[p] = M and nums[i] <= M for every 0 <= i < len(nums).
    Preconditions: len(nums) >= 1, len(nums) <= 100, 1 <= k <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1
      (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
      ∃ (r : Std.I64) (M : Int),
        Aegis.MaximizeSum.maximize_sum nums k = ok r ∧ IsSliceMax nums M ∧
          r.val = k.val * M + k.val * (k.val - 1) / 2 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ (r : Std.I64) (M : Int),
          Aegis.MaximizeSum.maximize_sum nums k = ok r ∧ IsSliceMax nums M ∧
            r.val = k.val * M + k.val * (k.val - 1) / 2) := by
    sorry

  /-- The function returns a result r; in particular, it does not panic or overflow for any input satisfying the preconditions.
    Preconditions: len(nums) >= 1, len(nums) <= 100, 1 <= k <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2
      (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
      ∃ (r : Std.I64), Aegis.MaximizeSum.maximize_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ (r : Std.I64), Aegis.MaximizeSum.maximize_sum nums k = ok r) := by
    sorry

  /-- The function returns r and there exists an index p with 0 <= p < len(nums) such that nums[i] <= nums[p] for every 0 <= i < len(nums), and r = sum_{j=0}^{k-1} (nums[p] + j).
    Preconditions: len(nums) >= 1, len(nums) <= 100, 1 <= k <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3
      (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
      ∃ (r : Std.I64) (p : Nat) (hp : p < nums.val.length),
        Aegis.MaximizeSum.maximize_sum nums k = ok r ∧
          (∀ (i : Nat) (hi : i < nums.val.length),
            (nums.val.get ⟨i, hi⟩).val ≤ (nums.val.get ⟨p, hp⟩).val) ∧
          r.val = ∑ j : Fin (k.val).toNat, ((nums.val.get ⟨p, hp⟩).val + (j : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ (r : Std.I64) (p : Nat) (hp : p < nums.val.length),
          Aegis.MaximizeSum.maximize_sum nums k = ok r ∧
            (∀ (i : Nat) (hi : i < nums.val.length),
              (nums.val.get ⟨i, hi⟩).val ≤ (nums.val.get ⟨p, hp⟩).val) ∧
            r.val = ∑ j : Fin (k.val).toNat, ((nums.val.get ⟨p, hp⟩).val + (j : Int))) := by
    sorry

  /-- The function returns r and, for every choice of nonnegative integers t_0, ..., t_{len(nums)-1} satisfying sum_{i=0}^{len(nums)-1} t_i = k, we have sum_{i=0}^{len(nums)-1} ( t_i*nums[i] + (t_i*(t_i-1))/2 ) <= r.
    Preconditions: len(nums) >= 1, len(nums) <= 100, 1 <= k <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4
      (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
      ∃ (r : Std.I64),
        Aegis.MaximizeSum.maximize_sum nums k = ok r ∧
          ∀ (t : Fin nums.val.length → Int),
            (∀ i : Fin nums.val.length, 0 ≤ t i) →
            (∑ i : Fin nums.val.length, t i) = k.val →
            (∑ i : Fin nums.val.length,
              (t i * (nums.val.get i).val + t i * (t i - 1) / 2)) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ (r : Std.I64),
          Aegis.MaximizeSum.maximize_sum nums k = ok r ∧
            ∀ (t : Fin nums.val.length → Int),
              (∀ i : Fin nums.val.length, 0 ≤ t i) →
              (∑ i : Fin nums.val.length, t i) = k.val →
              (∑ i : Fin nums.val.length,
                (t i * (nums.val.get i).val + t i * (t i - 1) / 2)) ≤ r.val) := by
    sorry

  /-- For admissible nums and k with 1 <= k < 100, if maximize_sum nums k = Result.ok r and maximize_sum nums (k+1) = Result.ok r', then r' = r + M + k, where M is the maximum value in nums.
    Preconditions: len(nums) >= 1, len(nums) <= 100, 1 <= k < 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5
      (nums : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk99 : k.val < 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100) :
      ∃ (M : Int), IsSliceMax nums M ∧
        ∀ (k1 : Std.I64), k1.val = k.val + 1 →
          ∀ (r r' : Std.I64),
            Aegis.MaximizeSum.maximize_sum nums k = ok r →
            Aegis.MaximizeSum.maximize_sum nums k1 = ok r' →
            r'.val = r.val + M + k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk99 : k.val < 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100), ∃ (M : Int), IsSliceMax nums M ∧
          ∀ (k1 : Std.I64), k1.val = k.val + 1 →
            ∀ (r r' : Std.I64),
              Aegis.MaximizeSum.maximize_sum nums k = ok r →
              Aegis.MaximizeSum.maximize_sum nums k1 = ok r' →
              r'.val = r.val + M + k.val) := by
    sorry

  /-- If maximize_sum nums k = Result.ok r and maximize_sum nums' k = Result.ok r', then r = r'.
    Preconditions: nums and nums' are nonempty slices, each of length at most 100; 1 <= k <= 100; every element of nums and of nums' lies in [1,100]; and max(nums) = max(nums'). -/
  theorem spec_6
      (nums nums' : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
      (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
      (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
      (hmax : ∃ M : Int, IsSliceMax nums M ∧ IsSliceMax nums' M) :
      ∀ (r r' : Std.I64),
        Aegis.MaximizeSum.maximize_sum nums k = ok r →
        Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
        r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
        (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
        (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
        (hmax : ∃ M : Int, IsSliceMax nums M ∧ IsSliceMax nums' M), ∀ (r r' : Std.I64),
          Aegis.MaximizeSum.maximize_sum nums k = ok r →
          Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
          r = r') := by
    sorry

  /-- If maximize_sum nums k = Result.ok r and maximize_sum nums' k = Result.ok r', then r' = r + k*c.
    Preconditions: nums and nums' are nonempty slices of the same length at most 100; 1 <= k <= 100; every element of both slices lies in [1,100]; and there is an integer c such that nums'[i] = nums[i] + c for every 0 <= i < len(nums). -/
  theorem spec_7
      (nums nums' : Slice Std.I64) (k : Std.I64) (c : Int)
      (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
      (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
      (hlen_eq : nums'.val.length = nums.val.length)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
      (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
      (hshift : ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
        (nums'.val.get ⟨i, hi'⟩).val = (nums.val.get ⟨i, hi⟩).val + c) :
      ∀ (r r' : Std.I64),
        Aegis.MaximizeSum.maximize_sum nums k = ok r →
        Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
        r'.val = r.val + k.val * c := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (c : Int)
        (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
        (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
        (hlen_eq : nums'.val.length = nums.val.length)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
        (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
        (hshift : ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
          (nums'.val.get ⟨i, hi'⟩).val = (nums.val.get ⟨i, hi⟩).val + c), ∀ (r r' : Std.I64),
          Aegis.MaximizeSum.maximize_sum nums k = ok r →
          Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
          r'.val = r.val + k.val * c) := by
    sorry

  /-- If maximize_sum nums k = Result.ok r and maximize_sum nums' k = Result.ok r', then r' = c*r - (c-1)*(k*(k-1))/2.
    Preconditions: nums and nums' are nonempty slices of the same length at most 100; 1 <= k <= 100; every element of both slices lies in [1,100]; and there is an integer c >= 1 such that nums'[i] = c*nums[i] for every 0 <= i < len(nums). -/
  theorem spec_8
      (nums nums' : Slice Std.I64) (k : Std.I64) (c : Int)
      (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
      (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
      (hlen_eq : nums'.val.length = nums.val.length)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
      (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
      (hc : 1 ≤ c)
      (hscale : ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
        (nums'.val.get ⟨i, hi'⟩).val = c * (nums.val.get ⟨i, hi⟩).val) :
      ∀ (r r' : Std.I64),
        Aegis.MaximizeSum.maximize_sum nums k = ok r →
        Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
        r'.val = c * r.val - (c - 1) * (k.val * (k.val - 1)) / 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (c : Int)
        (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
        (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
        (hlen_eq : nums'.val.length = nums.val.length)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
        (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
        (hc : 1 ≤ c)
        (hscale : ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
          (nums'.val.get ⟨i, hi'⟩).val = c * (nums.val.get ⟨i, hi⟩).val), ∀ (r r' : Std.I64),
          Aegis.MaximizeSum.maximize_sum nums k = ok r →
          Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
          r'.val = c * r.val - (c - 1) * (k.val * (k.val - 1)) / 2) := by
    sorry

  /-- If maximize_sum nums k = Result.ok r and maximize_sum nums' k = Result.ok r', then r < r'.
    Preconditions: nums and nums' are nonempty slices, each of length at most 100; 1 <= k <= 100; every element of both slices lies in [1,100]; and max(nums) < max(nums'). -/
  theorem spec_9
      (nums nums' : Slice Std.I64) (k : Std.I64)
      (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
      (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
      (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
      (helem : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
      (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
      (hmax : ∃ M M' : Int, IsSliceMax nums M ∧ IsSliceMax nums' M' ∧ M < M') :
      ∀ (r r' : Std.I64),
        Aegis.MaximizeSum.maximize_sum nums k = ok r →
        Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
        r.val < r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hne : 1 ≤ nums.val.length) (hne' : 1 ≤ nums'.val.length)
        (hlen : nums.val.length ≤ 100) (hlen' : nums'.val.length ≤ 100)
        (hk1 : 1 ≤ k.val) (hk100 : k.val ≤ 100)
        (helem : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100)
        (helem' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100)
        (hmax : ∃ M M' : Int, IsSliceMax nums M ∧ IsSliceMax nums' M' ∧ M < M'), ∀ (r r' : Std.I64),
          Aegis.MaximizeSum.maximize_sum nums k = ok r →
          Aegis.MaximizeSum.maximize_sum nums' k = ok r' →
          r.val < r'.val) := by
    sorry

  end AegisSpec.MaximizeSum
