import Aegis.CanReorderDoubled.Code.Funs

/-!
# Specifications of `Aegis.CanReorderDoubled.can_reorder_doubled`

LeetCode problem `array-of-doubled-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanReorderDoubled

  def sliceVals (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def countOf (l : List ℤ) (v : ℤ) : ℕ := l.countP (fun x => decide (x = v))

  def occ (arr : Slice Std.I64) (v : ℤ) : ℕ := countOf (sliceVals arr) v

  def IsDoubledPairs (b : List ℤ) : Prop :=
    ∀ (i : ℕ) (h : i < b.length / 2), b[2 * i + 1]'(by omega) = 2 * b[2 * i]'(by omega)

  /-- The function returns a result r and r = true if and only if there exists a list b of length len(arr) such that (1) b is a permutation of arr, i.e. for every integer v the number of indices i with b[i] = v equals the number of indices j with arr[j] = v, and (2) for every i with 0 <= i < len(arr)/2, b[2*i+1] = 2 * b[2*i].
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 30000, len(arr) is even, and for every i with 0 <= i < len(arr), -100000 <= arr[i] <= 100000. -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      ∃ r, Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r ∧
        (r = true ↔ ∃ b : List ℤ,
          b.length = arr.val.length ∧
          (∀ v : ℤ, countOf b v = occ arr v) ∧
          IsDoubledPairs b) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), ∃ r, Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r ∧
          (r = true ↔ ∃ b : List ℤ,
            b.length = arr.val.length ∧
            (∀ v : ℤ, countOf b v = occ arr v) ∧
            IsDoubledPairs b)) := by
    sorry

  /-- For every arr satisfying the preconditions, the function returns a result r (a Bool); it does not fail, panic, or overflow.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 30000, len(arr) is even, and for every i with 0 <= i < len(arr), -100000 <= arr[i] <= 100000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      ∃ r, Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), ∃ r, Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r) := by
    sorry

  /-- If can_reorder_doubled arr returns r and can_reorder_doubled arr' returns r', then r = r'.
    Preconditions: arr and arr' are slices satisfying the input constraints (2 <= len(arr), len(arr') <= 30000, even lengths, all entries in [-100000,100000]), and arr' is a permutation of arr, i.e. for every integer v the number of occurrences of v in arr' equals the number of occurrences of v in arr. -/
  theorem spec_3 (arr arr' : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
      (hlen_lower' : 2 ≤ arr'.val.length) (hlen_upper' : arr'.val.length ≤ 30000)
      (hlen_even' : arr'.val.length % 2 = 0)
      (hbound' : ∀ (i : ℕ) (h : i < arr'.val.length),
        -100000 ≤ (arr'.val[i]'h).val ∧ (arr'.val[i]'h).val ≤ 100000)
      (hperm : ∀ v : ℤ, occ arr' v = occ arr v) :
      ∀ (r r' : Bool), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r →
        Aegis.CanReorderDoubled.can_reorder_doubled arr' = ok r' → r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr arr' : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
        (hlen_lower' : 2 ≤ arr'.val.length) (hlen_upper' : arr'.val.length ≤ 30000)
        (hlen_even' : arr'.val.length % 2 = 0)
        (hbound' : ∀ (i : ℕ) (h : i < arr'.val.length),
          -100000 ≤ (arr'.val[i]'h).val ∧ (arr'.val[i]'h).val ≤ 100000)
        (hperm : ∀ v : ℤ, occ arr' v = occ arr v), ∀ (r r' : Bool), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r →
          Aegis.CanReorderDoubled.can_reorder_doubled arr' = ok r' → r = r') := by
    sorry

  /-- The function returns true.
    Preconditions: arr satisfies the input constraints and for every i with 0 <= i < len(arr), arr[i] = 0. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
      (hzero : ∀ (i : ℕ) (h : i < arr.val.length), (arr.val[i]'h).val = 0) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
        (hzero : ∀ (i : ℕ) (h : i < arr.val.length), (arr.val[i]'h).val = 0), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true) := by
    sorry

  /-- The function returns false.
    Preconditions: arr satisfies the input constraints and the number of indices i with 0 <= i < len(arr) and arr[i] = 0 is odd. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
      (hodd : occ arr 0 % 2 = 1) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
        (hodd : occ arr 0 % 2 = 1), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok false) := by
    sorry

  /-- Whenever the function returns true on arr, the mathematical sum sum_{i=0}^{len(arr)-1} arr[i] is divisible by 3.
    Preconditions: arr satisfies the input constraints. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
        (3 : ℤ) ∣ (sliceVals arr).sum := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
          (3 : ℤ) ∣ (sliceVals arr).sum) := by
    sorry

  /-- The function returns true if and only if arr[0] = 2 * arr[1] or arr[1] = 2 * arr[0].
    Preconditions: arr satisfies the input constraints and len(arr) = 2. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
      (hlen : arr.val.length = 2) :
      ∃ r, Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r ∧
        (r = true ↔
          (arr.val[0]'(by omega)).val = 2 * (arr.val[1]'(by omega)).val ∨
          (arr.val[1]'(by omega)).val = 2 * (arr.val[0]'(by omega)).val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
        (hlen : arr.val.length = 2), ∃ r, Aegis.CanReorderDoubled.can_reorder_doubled arr = ok r ∧
          (r = true ↔
            (arr.val[0]'(by omega)).val = 2 * (arr.val[1]'(by omega)).val ∨
            (arr.val[1]'(by omega)).val = 2 * (arr.val[0]'(by omega)).val)) := by
    sorry

  /-- Whenever the function returns true on arr, there exists a list c of length len(arr)/2 such that for every integer v, the number of indices i with arr[i] = v equals the number of indices j with c[j] = v plus the number of indices j with 2*c[j] = v.
    Preconditions: arr satisfies the input constraints. -/
  theorem spec_8 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
        ∃ c : List ℤ, c.length = arr.val.length / 2 ∧
          ∀ v : ℤ, occ arr v = countOf c v + countOf (c.map (fun x => 2 * x)) v := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
          ∃ c : List ℤ, c.length = arr.val.length / 2 ∧
            ∀ v : ℤ, occ arr v = countOf c v + countOf (c.map (fun x => 2 * x)) v) := by
    sorry

  /-- Whenever the function returns true on arr, it returns true on arr'.
    Preconditions: arr satisfies the input constraints and len(arr) <= 29998; a is an integer with -50000 <= a <= 50000; arr' is a slice satisfying the input constraints whose multiset is the multiset of arr together with one additional occurrence of a and one additional occurrence of 2*a. -/
  theorem spec_9 (arr arr' : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
      (hlen_thin : arr.val.length ≤ 29998)
      (a : ℤ) (ha_lower : -50000 ≤ a) (ha_upper : a ≤ 50000)
      (hlen_lower' : 2 ≤ arr'.val.length) (hlen_upper' : arr'.val.length ≤ 30000)
      (hlen_even' : arr'.val.length % 2 = 0)
      (hbound' : ∀ (i : ℕ) (h : i < arr'.val.length),
        -100000 ≤ (arr'.val[i]'h).val ∧ (arr'.val[i]'h).val ≤ 100000)
      (hms : ∀ v : ℤ,
        occ arr' v = occ arr v + (if v = a then 1 else 0) + (if v = 2 * a then 1 else 0)) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
        Aegis.CanReorderDoubled.can_reorder_doubled arr' = ok true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr arr' : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000)
        (hlen_thin : arr.val.length ≤ 29998)
        (a : ℤ) (ha_lower : -50000 ≤ a) (ha_upper : a ≤ 50000)
        (hlen_lower' : 2 ≤ arr'.val.length) (hlen_upper' : arr'.val.length ≤ 30000)
        (hlen_even' : arr'.val.length % 2 = 0)
        (hbound' : ∀ (i : ℕ) (h : i < arr'.val.length),
          -100000 ≤ (arr'.val[i]'h).val ∧ (arr'.val[i]'h).val ≤ 100000)
        (hms : ∀ v : ℤ,
          occ arr' v = occ arr v + (if v = a then 1 else 0) + (if v = 2 * a then 1 else 0)), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
          Aegis.CanReorderDoubled.can_reorder_doubled arr' = ok true) := by
    sorry

  /-- Whenever the function returns true on arr, for every integer x that is odd and nonzero, the number of indices i with arr[i] = x is at most the number of indices i with arr[i] = 2*x.
    Preconditions: arr satisfies the input constraints. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
        ∀ x : ℤ, Odd x → x ≠ 0 → occ arr x ≤ occ arr (2 * x) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
          ∀ x : ℤ, Odd x → x ≠ 0 → occ arr x ≤ occ arr (2 * x)) := by
    sorry

  /-- Whenever the function returns true on arr, the number of indices i with 0 <= i < len(arr) and arr[i] > 0 is even.
    Preconditions: arr satisfies the input constraints. -/
  theorem spec_11 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
        ((sliceVals arr).countP (fun x => decide (0 < x))) % 2 = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
          ((sliceVals arr).countP (fun x => decide (0 < x))) % 2 = 0) := by
    sorry

  /-- Whenever the function returns true on arr, for every even integer x, the number of indices i with arr[i] = x is at most the number of indices i with arr[i] = 2*x plus the number of indices i with arr[i] = x/2.
    Preconditions: arr satisfies the input constraints. -/
  theorem spec_12 (arr : Slice Std.I64)
      (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
      (hlen_even : arr.val.length % 2 = 0)
      (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
        -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000) :
      Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
        ∀ x : ℤ, Even x → occ arr x ≤ occ arr (2 * x) + occ arr (x / 2) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 2 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 30000)
        (hlen_even : arr.val.length % 2 = 0)
        (hbound : ∀ (i : ℕ) (h : i < arr.val.length),
          -100000 ≤ (arr.val[i]'h).val ∧ (arr.val[i]'h).val ≤ 100000), Aegis.CanReorderDoubled.can_reorder_doubled arr = ok true →
          ∀ x : ℤ, Even x → occ arr x ≤ occ arr (2 * x) + occ arr (x / 2)) := by
    sorry

  end AegisSpec.CanReorderDoubled
