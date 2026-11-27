import Aegis.IsGoodArray.Code.Funs

/-!
# Specifications of `Aegis.IsGoodArray.is_good_array`

LeetCode problem `check-if-it-is-a-good-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aegis.IsGoodArray (is_good_array)

  namespace AegisSpec.IsGoodArray

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def DvdAll (d : Int) (l : List Int) : Prop := ∀ x ∈ l, d ∣ x

  def IsGCDAll (g : Int) (l : List Int) : Prop :=
    0 < g ∧ DvdAll g l ∧ ∀ d : Int, 0 < d → DvdAll d l → d ∣ g

  def IsGCD2 (g : Int) (x y : Int) : Prop := IsGCDAll g [x, y]

  def IsPrimeInt (p : Int) : Prop := 1 < p ∧ ∀ d : Int, 0 < d → d ∣ p → d = 1 ∨ d = p

  def nth (l : List Int) (i : Nat) : Int := l.getD i 0

  def dot : List Int → List Int → Int
    | [], _ => 0
    | _ :: _, [] => 0
    | x :: xs, y :: ys => x * y + dot xs ys

  /-- Let g be the greatest positive integer that divides nums[i] for every i with 0 <= i < len(nums). For every nums satisfying the preconditions, the function returns a result r and r = true if and only if g = 1.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000) :
      ∃ r : Bool, is_good_array nums = ok r ∧ (r = true ↔ IsGCDAll 1 (contents nums)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000), ∃ r : Bool, is_good_array nums = ok r ∧ (r = true ↔ IsGCDAll 1 (contents nums))) := by
    sorry

  /-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000) :
      ∃ r : Bool, is_good_array nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000), ∃ r : Bool, is_good_array nums = ok r) := by
    sorry

  /-- For every nums satisfying the preconditions, whenever the function returns true, there exist integers c_0, c_1, ..., c_{len(nums)-1} such that sum_{i=0}^{len(nums)-1} c_i * nums[i] = 1.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000) :
      ∀ r : Bool, is_good_array nums = ok r → r = true →
        ∃ cs : List Int, cs.length = (contents nums).length ∧
          dot cs (contents nums) = 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000), ∀ r : Bool, is_good_array nums = ok r → r = true →
          ∃ cs : List Int, cs.length = (contents nums).length ∧
            dot cs (contents nums) = 1) := by
    sorry

  /-- For every nums satisfying the preconditions, if there exists an integer d with d > 1 such that d divides nums[i] for every i with 0 <= i < len(nums), then the function returns false.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (hd : ∃ d : Int, 1 < d ∧ DvdAll d (contents nums)) :
      ∃ r : Bool, is_good_array nums = ok r ∧ r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (hd : ∃ d : Int, 1 < d ∧ DvdAll d (contents nums)), ∃ r : Bool, is_good_array nums = ok r ∧ r = false) := by
    sorry

  /-- For every nums satisfying the preconditions and every i with 0 <= i < len(nums), if nums[i] = 1, then the function returns true.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (i : Nat) (hi : i < (contents nums).length) (h1 : nth (contents nums) i = 1) :
      ∃ r : Bool, is_good_array nums = ok r ∧ r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (i : Nat) (hi : i < (contents nums).length) (h1 : nth (contents nums) i = 1), ∃ r : Bool, is_good_array nums = ok r ∧ r = true) := by
    sorry

  /-- For every nums satisfying the preconditions and every i, j with 0 <= i < len(nums), 0 <= j < len(nums), and i != j, if gcd(nums[i], nums[j]) = 1, where gcd(x, y) is the greatest positive integer dividing both x and y, then the function returns true.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (i j : Nat)
      (hi : i < (contents nums).length) (hj : j < (contents nums).length) (hij : i ≠ j)
      (hgcd : IsGCD2 1 (nth (contents nums) i) (nth (contents nums) j)) :
      ∃ r : Bool, is_good_array nums = ok r ∧ r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (i j : Nat)
        (hi : i < (contents nums).length) (hj : j < (contents nums).length) (hij : i ≠ j)
        (hgcd : IsGCD2 1 (nth (contents nums) i) (nth (contents nums) j)), ∃ r : Bool, is_good_array nums = ok r ∧ r = true) := by
    sorry

  /-- For every nums satisfying the preconditions and every bijection p from {0, ..., len(nums)-1} to itself, let ys be the array with len(ys) = len(nums) and ys[k] = nums[p(k)] for every k with 0 <= k < len(nums). Then whenever the function returns results r on nums and r' on ys, r = r'.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums ys : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (hys_len : (contents ys).length = (contents nums).length)
      (p : Nat → Nat)
      (hp_lt : ∀ a, a < (contents nums).length → p a < (contents nums).length)
      (hp_inj : ∀ a b, a < (contents nums).length → b < (contents nums).length → p a = p b → a = b)
      (hys : ∀ k, k < (contents nums).length → nth (contents ys) k = nth (contents nums) (p k)) :
      ∀ r r' : Bool, is_good_array nums = ok r → is_good_array ys = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums ys : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (hys_len : (contents ys).length = (contents nums).length)
        (p : Nat → Nat)
        (hp_lt : ∀ a, a < (contents nums).length → p a < (contents nums).length)
        (hp_inj : ∀ a b, a < (contents nums).length → b < (contents nums).length → p a = p b → a = b)
        (hys : ∀ k, k < (contents nums).length → nth (contents ys) k = nth (contents nums) (p k)), ∀ r r' : Bool, is_good_array nums = ok r → is_good_array ys = ok r' → r = r') := by
    sorry

  /-- For every nums satisfying the preconditions, every value v, and every pair of distinct indices i, j with nums[i] = v and nums[j] = v, let xs be the array obtained from nums by deleting the element at index j: len(xs) = len(nums)-1, xs[k] = nums[k] for 0 <= k < j, and xs[k] = nums[k+1] for j <= k < len(xs). Then whenever the function returns results r on nums and r' on xs, r = r'.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums xs : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (v : Int) (i j : Nat)
      (hi : i < (contents nums).length) (hj : j < (contents nums).length) (hij : i ≠ j)
      (hvi : nth (contents nums) i = v) (hvj : nth (contents nums) j = v)
      (hxs_len : (contents xs).length = (contents nums).length - 1)
      (hxs_left : ∀ k, k < j → nth (contents xs) k = nth (contents nums) k)
      (hxs_right : ∀ k, j ≤ k → k < (contents xs).length →
        nth (contents xs) k = nth (contents nums) (k + 1)) :
      ∀ r r' : Bool, is_good_array nums = ok r → is_good_array xs = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums xs : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (v : Int) (i j : Nat)
        (hi : i < (contents nums).length) (hj : j < (contents nums).length) (hij : i ≠ j)
        (hvi : nth (contents nums) i = v) (hvj : nth (contents nums) j = v)
        (hxs_len : (contents xs).length = (contents nums).length - 1)
        (hxs_left : ∀ k, k < j → nth (contents xs) k = nth (contents nums) k)
        (hxs_right : ∀ k, j ≤ k → k < (contents xs).length →
          nth (contents xs) k = nth (contents nums) (k + 1)), ∀ r r' : Bool, is_good_array nums = ok r → is_good_array xs = ok r' → r = r') := by
    sorry

  /-- For every nums satisfying the preconditions with len(nums) < 100000, and every integer k with 1 <= k <= 1000000000, if the function returns true on nums, then the function returns true on the array nums' of length len(nums)+1 with nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[len(nums)] = k.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums nums' : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (hlen_lt : (contents nums).length < 100000)
      (k : Int) (hk_low : 1 ≤ k) (hk_high : k ≤ 1000000000)
      (h'len : (contents nums').length = (contents nums).length + 1)
      (h'prefix : ∀ i, i < (contents nums).length →
        nth (contents nums') i = nth (contents nums) i)
      (h'last : nth (contents nums') (contents nums).length = k) :
      ∀ r : Bool, is_good_array nums = ok r → r = true →
        ∃ r' : Bool, is_good_array nums' = ok r' ∧ r' = true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (hlen_lt : (contents nums).length < 100000)
        (k : Int) (hk_low : 1 ≤ k) (hk_high : k ≤ 1000000000)
        (h'len : (contents nums').length = (contents nums).length + 1)
        (h'prefix : ∀ i, i < (contents nums).length →
          nth (contents nums') i = nth (contents nums) i)
        (h'last : nth (contents nums') (contents nums).length = k), ∀ r : Bool, is_good_array nums = ok r → r = true →
          ∃ r' : Bool, is_good_array nums' = ok r' ∧ r' = true) := by
    sorry

  /-- For every nums satisfying the preconditions, if the function returns false on nums, then for every nonempty subsequence xs of nums, the function returns false on xs. Here a nonempty subsequence is defined by indices i_0 < i_1 < ... < i_{m-1} with m >= 1 and 0 <= i_0 <= i_{m-1} < len(nums), and xs[k] = nums[i_k] for 0 <= k < m.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_10 (nums xs : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (m : Nat) (hm : 1 ≤ m) (idx : Nat → Nat)
      (hidx_mono : ∀ a b, a < m → b < m → a < b → idx a < idx b)
      (hidx_bound : ∀ a, a < m → idx a < (contents nums).length)
      (hxs_len : (contents xs).length = m)
      (hxs : ∀ a, a < m → nth (contents xs) a = nth (contents nums) (idx a)) :
      ∀ r : Bool, is_good_array nums = ok r → r = false →
        ∃ r' : Bool, is_good_array xs = ok r' ∧ r' = false := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums xs : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (m : Nat) (hm : 1 ≤ m) (idx : Nat → Nat)
        (hidx_mono : ∀ a b, a < m → b < m → a < b → idx a < idx b)
        (hidx_bound : ∀ a, a < m → idx a < (contents nums).length)
        (hxs_len : (contents xs).length = m)
        (hxs : ∀ a, a < m → nth (contents xs) a = nth (contents nums) (idx a)), ∀ r : Bool, is_good_array nums = ok r → r = false →
          ∃ r' : Bool, is_good_array xs = ok r' ∧ r' = false) := by
    sorry

  /-- For every two arrays nums and ys satisfying the preconditions, let g be the greatest positive integer dividing every element of nums, and let h be the greatest positive integer dividing every element of ys. If g = h, then whenever the function returns results r on nums and r' on ys, r = r'.
    Preconditions: nums and ys are slices of 64-bit integers with 1 <= len(nums) <= 100000 and 1 <= len(ys) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and for every i with 0 <= i < len(ys), 1 <= ys[i] <= 1000000000. -/
  theorem spec_11 (nums ys : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
      (hys_len : 1 ≤ (contents ys).length)
      (hys_len_max : (contents ys).length ≤ 100000)
      (hys_range : ∀ y ∈ contents ys, 1 ≤ y ∧ y ≤ 1000000000)
      (g h : Int) (hg : IsGCDAll g (contents nums)) (hh : IsGCDAll h (contents ys))
      (hgh : g = h) :
      ∀ r r' : Bool, is_good_array nums = ok r → is_good_array ys = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums ys : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000)
        (hys_len : 1 ≤ (contents ys).length)
        (hys_len_max : (contents ys).length ≤ 100000)
        (hys_range : ∀ y ∈ contents ys, 1 ≤ y ∧ y ≤ 1000000000)
        (g h : Int) (hg : IsGCDAll g (contents nums)) (hh : IsGCDAll h (contents ys))
        (hgh : g = h), ∀ r r' : Bool, is_good_array nums = ok r → is_good_array ys = ok r' → r = r') := by
    sorry

  /-- For every nums satisfying the preconditions, if the function returns false on nums, then there exists a prime p, meaning an integer p > 1 whose only positive divisors are 1 and p, such that p divides nums[i] for every i with 0 <= i < len(nums).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 1 ≤ (contents nums).length)
      (hlen_max : (contents nums).length ≤ 100000)
      (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000) :
      ∀ r : Bool, is_good_array nums = ok r → r = false →
        ∃ p : Int, IsPrimeInt p ∧ DvdAll p (contents nums) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ (contents nums).length)
        (hlen_max : (contents nums).length ≤ 100000)
        (hrange : ∀ x ∈ contents nums, 1 ≤ x ∧ x ≤ 1000000000), ∀ r : Bool, is_good_array nums = ok r → r = false →
          ∃ p : Int, IsPrimeInt p ∧ DvdAll p (contents nums)) := by
    sorry

  end AegisSpec.IsGoodArray
