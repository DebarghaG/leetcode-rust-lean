import Aegis.DoesValidArrayExist.Code.Funs

/-!
# Specifications of `Aegis.DoesValidArrayExist.does_valid_array_exist`

LeetCode problem `neighboring-bitwise-xor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DoesValidArrayExist

  def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def IsBinary (l : List ℤ) : Prop := ∀ x ∈ l, x = 0 ∨ x = 1

  def xorBit (a b : ℤ) : ℤ := if a = b then 0 else 1

  def countOnes (l : List ℤ) : ℕ := l.countP (fun x => decide (x = 1))

  def IsXorPreimage (derived original : List ℤ) : Prop :=
    ∀ (i : ℕ), i < derived.length →
      derived.getD i 0 = xorBit (original.getD i 0) (original.getD ((i + 1) % derived.length) 0)

  /-- The function returns a result r (it does not fail), and r = true if and only if there exists a binary array original of length n such that for every i with 0 <= i < n, derived[i] = original[i] XOR original[(i + 1) mod n]. Equivalently, r = false if and only if no such binary array original exists.
    Preconditions: Let n = len(derived). We have n >= 1, and for every i with 0 <= i < n, derived[i] is either 0 or 1. -/
  theorem spec_1 (derived : Slice Std.I64)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1) :
      ∃ (r : Bool), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r ∧
        (r = true ↔ ∃ (original : List ℤ),
          original.length = (vals derived).length ∧ IsBinary original ∧
            IsXorPreimage (vals derived) original) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (derived : Slice Std.I64)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1), ∃ (r : Bool), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r ∧
          (r = true ↔ ∃ (original : List ℤ),
            original.length = (vals derived).length ∧ IsBinary original ∧
              IsXorPreimage (vals derived) original)) := by
    sorry

  /-- The function returns a result r for every derived satisfying the preconditions; in particular, it does not fail, panic, overflow, or perform an out-of-bounds access.
    Preconditions: Let n = len(derived). We have n >= 1, and for every i with 0 <= i < n, derived[i] is either 0 or 1. -/
  theorem spec_2 (derived : Slice Std.I64)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1) :
      ∃ (r : Bool), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (derived : Slice Std.I64)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1), ∃ (r : Bool), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r) := by
    sorry

  /-- The function returns a result r, and r = true if and only if the number of indices i with 0 <= i < n and derived[i] = 1 is even. Equivalently, r = true if and only if the sum of all entries derived[i] is even, or equivalently the XOR of all entries is 0.
    Preconditions: Let n = len(derived). We have n >= 1, and for every i with 0 <= i < n, derived[i] is either 0 or 1. -/
  theorem spec_3 (derived : Slice Std.I64)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1) :
      ∃ (r : Bool), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r ∧
        (r = true ↔ countOnes (vals derived) % 2 = 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (derived : Slice Std.I64)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1), ∃ (r : Bool), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r ∧
          (r = true ↔ countOnes (vals derived) % 2 = 0)) := by
    sorry

  /-- The function returns true on derived.
    Preconditions: Let n = len(derived) >= 1. The array derived is binary, the array original has length n and is binary, and for every i with 0 <= i < n, derived[i] = original[i] XOR original[(i + 1) mod n]. -/
  theorem spec_4 (derived : Slice Std.I64) (original : List ℤ)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
      (hlen : original.length = (vals derived).length)
      (hbin_original : IsBinary original)
      (hxor : IsXorPreimage (vals derived) original) :
      Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (derived : Slice Std.I64) (original : List ℤ)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
        (hlen : original.length = (vals derived).length)
        (hbin_original : IsBinary original)
        (hxor : IsXorPreimage (vals derived) original), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok true) := by
    sorry

  /-- Whenever the function returns true on derived, there exists a binary array original of length n such that for every i with 0 <= i < n, derived[i] = original[i] XOR original[(i + 1) mod n].
    Preconditions: Let n = len(derived) >= 1, and for every i with 0 <= i < n, derived[i] is either 0 or 1. -/
  theorem spec_5 (derived : Slice Std.I64)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1) :
      Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok true →
        ∃ (original : List ℤ),
          original.length = (vals derived).length ∧ IsBinary original ∧
            IsXorPreimage (vals derived) original := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (derived : Slice Std.I64)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1), Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok true →
          ∃ (original : List ℤ),
            original.length = (vals derived).length ∧ IsBinary original ∧
              IsXorPreimage (vals derived) original) := by
    sorry

  /-- If the function returns r_a on input a and r_b on input b, then r_a = r_b.
    Preconditions: Let a and b be two binary arrays of the same length n >= 1, and suppose a and b have the same number of entries equal to 1. -/
  theorem spec_6 (a b : Slice Std.I64)
      (hn : 1 ≤ a.val.length)
      (hlen : b.val.length = a.val.length)
      (hbin_a : ∀ (i : ℕ) (hi : i < a.val.length),
        (a.val[i]).val = 0 ∨ (a.val[i]).val = 1)
      (hbin_b : ∀ (i : ℕ) (hi : i < b.val.length),
        (b.val[i]).val = 0 ∨ (b.val[i]).val = 1)
      (hcount : countOnes (vals a) = countOnes (vals b))
      (r_a r_b : Bool)
      (hr_a : Aegis.DoesValidArrayExist.does_valid_array_exist a = ok r_a)
      (hr_b : Aegis.DoesValidArrayExist.does_valid_array_exist b = ok r_b) :
      r_a = r_b := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b : Slice Std.I64)
        (hn : 1 ≤ a.val.length)
        (hlen : b.val.length = a.val.length)
        (hbin_a : ∀ (i : ℕ) (hi : i < a.val.length),
          (a.val[i]).val = 0 ∨ (a.val[i]).val = 1)
        (hbin_b : ∀ (i : ℕ) (hi : i < b.val.length),
          (b.val[i]).val = 0 ∨ (b.val[i]).val = 1)
        (hcount : countOnes (vals a) = countOnes (vals b))
        (r_a r_b : Bool)
        (hr_a : Aegis.DoesValidArrayExist.does_valid_array_exist a = ok r_a)
        (hr_b : Aegis.DoesValidArrayExist.does_valid_array_exist b = ok r_b), r_a = r_b) := by
    sorry

  /-- If the function returns r on derived and r2 on derived2, then r2 = not r.
    Preconditions: Let derived be a binary array of length n >= 1. Let j satisfy 0 <= j < n. Let derived2 be the binary array of length n with derived2[j] = 1 - derived[j] and derived2[i] = derived[i] for every i with 0 <= i < n and i != j. -/
  theorem spec_7 (derived derived2 : Slice Std.I64) (j : ℕ)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
      (hlen : derived2.val.length = derived.val.length)
      (hbin2 : ∀ (i : ℕ) (hi : i < derived2.val.length),
        (derived2.val[i]).val = 0 ∨ (derived2.val[i]).val = 1)
      (hj : j < derived.val.length)
      (hflip : ∀ (i : ℕ) (hi : i < derived.val.length) (hi2 : i < derived2.val.length),
        (derived2.val[i]).val = if i = j then 1 - (derived.val[i]).val else (derived.val[i]).val)
      (r r2 : Bool)
      (hr : Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r)
      (hr2 : Aegis.DoesValidArrayExist.does_valid_array_exist derived2 = ok r2) :
      r2 = !r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (derived derived2 : Slice Std.I64) (j : ℕ)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
        (hlen : derived2.val.length = derived.val.length)
        (hbin2 : ∀ (i : ℕ) (hi : i < derived2.val.length),
          (derived2.val[i]).val = 0 ∨ (derived2.val[i]).val = 1)
        (hj : j < derived.val.length)
        (hflip : ∀ (i : ℕ) (hi : i < derived.val.length) (hi2 : i < derived2.val.length),
          (derived2.val[i]).val = if i = j then 1 - (derived.val[i]).val else (derived.val[i]).val)
        (r r2 : Bool)
        (hr : Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r)
        (hr2 : Aegis.DoesValidArrayExist.does_valid_array_exist derived2 = ok r2), r2 = !r) := by
    sorry

  /-- If the function returns r on derived and r_ext on extended, then r_ext = r.
    Preconditions: Let derived be a binary array of length n >= 1. Let extended be the binary array of length n + 1 with extended[i] = derived[i] for every i with 0 <= i < n and extended[n] = 0. -/
  theorem spec_8 (derived extended : Slice Std.I64)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
      (hlen : extended.val.length = derived.val.length + 1)
      (hbin_extended : ∀ (i : ℕ) (hi : i < extended.val.length),
        (extended.val[i]).val = 0 ∨ (extended.val[i]).val = 1)
      (hagrees : ∀ (i : ℕ) (hi : i < derived.val.length) (hi2 : i < extended.val.length),
        (extended.val[i]).val = (derived.val[i]).val)
      (hbound : derived.val.length < extended.val.length)
      (hlast : (extended.val[derived.val.length]).val = 0)
      (r r_ext : Bool)
      (hr : Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r)
      (hr_ext : Aegis.DoesValidArrayExist.does_valid_array_exist extended = ok r_ext) :
      r_ext = r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (derived extended : Slice Std.I64)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
        (hlen : extended.val.length = derived.val.length + 1)
        (hbin_extended : ∀ (i : ℕ) (hi : i < extended.val.length),
          (extended.val[i]).val = 0 ∨ (extended.val[i]).val = 1)
        (hagrees : ∀ (i : ℕ) (hi : i < derived.val.length) (hi2 : i < extended.val.length),
          (extended.val[i]).val = (derived.val[i]).val)
        (hbound : derived.val.length < extended.val.length)
        (hlast : (extended.val[derived.val.length]).val = 0)
        (r r_ext : Bool)
        (hr : Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r)
        (hr_ext : Aegis.DoesValidArrayExist.does_valid_array_exist extended = ok r_ext), r_ext = r) := by
    sorry

  /-- If the function returns r on derived and r_ext on extended, then r_ext = not r.
    Preconditions: Let derived be a binary array of length n >= 1. Let extended be the binary array of length n + 1 with extended[i] = derived[i] for every i with 0 <= i < n and extended[n] = 1. -/
  theorem spec_9 (derived extended : Slice Std.I64)
      (hn : 1 ≤ derived.val.length)
      (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
        (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
      (hlen : extended.val.length = derived.val.length + 1)
      (hbin_extended : ∀ (i : ℕ) (hi : i < extended.val.length),
        (extended.val[i]).val = 0 ∨ (extended.val[i]).val = 1)
      (hagrees : ∀ (i : ℕ) (hi : i < derived.val.length) (hi2 : i < extended.val.length),
        (extended.val[i]).val = (derived.val[i]).val)
      (hbound : derived.val.length < extended.val.length)
      (hlast : (extended.val[derived.val.length]).val = 1)
      (r r_ext : Bool)
      (hr : Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r)
      (hr_ext : Aegis.DoesValidArrayExist.does_valid_array_exist extended = ok r_ext) :
      r_ext = !r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (derived extended : Slice Std.I64)
        (hn : 1 ≤ derived.val.length)
        (hbin : ∀ (i : ℕ) (hi : i < derived.val.length),
          (derived.val[i]).val = 0 ∨ (derived.val[i]).val = 1)
        (hlen : extended.val.length = derived.val.length + 1)
        (hbin_extended : ∀ (i : ℕ) (hi : i < extended.val.length),
          (extended.val[i]).val = 0 ∨ (extended.val[i]).val = 1)
        (hagrees : ∀ (i : ℕ) (hi : i < derived.val.length) (hi2 : i < extended.val.length),
          (extended.val[i]).val = (derived.val[i]).val)
        (hbound : derived.val.length < extended.val.length)
        (hlast : (extended.val[derived.val.length]).val = 1)
        (r r_ext : Bool)
        (hr : Aegis.DoesValidArrayExist.does_valid_array_exist derived = ok r)
        (hr_ext : Aegis.DoesValidArrayExist.does_valid_array_exist extended = ok r_ext), r_ext = !r) := by
    sorry

  end AegisSpec.DoesValidArrayExist
