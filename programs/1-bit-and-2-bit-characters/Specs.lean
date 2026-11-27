import Aegis.IsOneBitCharacter.Code.Funs

/-!
# Specifications of `Aegis.IsOneBitCharacter.is_one_bit_character`

LeetCode problem `1-bit-and-2-bit-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsOneBitCharacter

def bitAt (l : List Std.I64) (i : ℕ) : Option ℤ := (l[i]?).map (fun x => x.val)

def suffixOnesLen (l : List Std.I64) : ℕ :=
  (l.dropLast.reverse.takeWhile (fun x => x.val = 1)).length

def mkSlice (l : List Std.I64) (h : l.length ≤ Std.Usize.max) : Slice Std.I64 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

@[simp] theorem mkSlice_val (l : List Std.I64) (h : l.length ≤ Std.Usize.max) :
    (mkSlice l h).val = l := by
  simp [mkSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

def dropSlice (bits : Slice Std.I64) (i : ℕ) : Slice Std.I64 :=
  mkSlice (bits.val.drop i) (by
    have hlen : bits.val.length = bits.leng := by
      simpa [Slice.val] using Aeneas.Data.ListN.ListN_length bits.list
    have hbound := bits.bound
    simp only [List.length_drop]
    omega)

@[simp] theorem dropSlice_val (bits : Slice Std.I64) (i : ℕ) :
    (dropSlice bits i).val = bits.val.drop i := by
  simp [dropSlice]

def consSlice (x y : Std.I64) (bits : Slice Std.I64)
    (h : bits.val.length + 2 ≤ Std.Usize.max) : Slice Std.I64 :=
  mkSlice (x :: y :: bits.val) (by
    simp only [List.length_cons]
    omega)

@[simp] theorem consSlice_val (x y : Std.I64) (bits : Slice Std.I64)
    (h : bits.val.length + 2 ≤ Std.Usize.max) :
    (consSlice x y bits h).val = x :: y :: bits.val := by
  simp [consSlice]

def blocksFrom (start : ℕ) : List Std.I64 → List (ℕ × ℕ)
  | [] => []
  | [_] => [(start, 1)]
  | a :: b :: rest =>
      if a.val = 0 then
        (start, 1) :: blocksFrom (start + 1) (b :: rest)
      else
        (start, 2) :: blocksFrom (start + 2) rest

def blocks (l : List Std.I64) : List (ℕ × ℕ) := blocksFrom 0 l

def finalBlock (l : List Std.I64) : Option (ℕ × ℕ) := (blocks l).reverse.head?

def EndsWithOneBitBlock (l : List Std.I64) (n : ℕ) : Prop :=
  finalBlock l = some (n - 1, 1)

def EndsWithTwoBitBlock (l : List Std.I64) (n : ℕ) : Prop :=
  finalBlock l = some (n - 2, 2)

/-- The function returns a result r (it does not fail). Let k be the unique integer with 0 <= k <= n-1 such that bits[j] = 1 for every j with n-1-k <= j <= n-2, and either n-1-k = 0 or bits[n-2-k] = 0; this k is the length of the maximal contiguous suffix of 1s immediately before the final 0. Then r = true if and only if k is even. Equivalently, in the unique decomposition of the whole array into contiguous blocks each equal to [0], [1,0], or [1,1], r = true exactly when the final block is the one-bit block [0] at index n-1, and r = false exactly when the final block is the two-bit block [1,0] at indices n-2 and n-1.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. -/
theorem spec_1 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      (r = true ↔ suffixOnesLen bits.val % 2 = 0) ∧
      (r = true ↔ EndsWithOneBitBlock bits.val n) ∧
      (r = false ↔ EndsWithTwoBitBlock bits.val n) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      (r = true ↔ suffixOnesLen bits.val % 2 = 0) ∧
      (r = true ↔ EndsWithOneBitBlock bits.val n) ∧
      (r = false ↔ EndsWithTwoBitBlock bits.val n)) := by
  sorry

/-- The function returns a result r and does not fail (no panic, overflow, out-of-bounds access, or other failure) for every input satisfying the preconditions.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. -/
theorem spec_2 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r) := by
  sorry

/-- The function returns true.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. n = 1. -/
theorem spec_3 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : n = 1) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : n = 1), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧ r = true) := by
  sorry

/-- The function returns false.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. n >= 2, bits[n-2] = 1, and (n = 2 or bits[n-3] = 0). -/
theorem spec_4 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : 2 ≤ n)
    (hpenult : bitAt bits.val (n - 2) = some 1)
    (hprev : n = 2 ∨ bitAt bits.val (n - 3) = some 0) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧ r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : 2 ≤ n)
    (hpenult : bitAt bits.val (n - 2) = some 1)
    (hprev : n = 2 ∨ bitAt bits.val (n - 3) = some 0), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧ r = false) := by
  sorry

/-- The function returns true if and only if n is odd.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. For every i with 0 <= i < n-1, bits[i] = 1. -/
theorem spec_5 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hall : ∀ i, i < n - 1 → bitAt bits.val i = some 1) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      (r = true ↔ n % 2 = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hall : ∀ i, i < n - 1 → bitAt bits.val i = some 1), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      (r = true ↔ n % 2 = 1)) := by
  sorry

/-- Let s be the slice bits[1..n) (indices 1 through n-1). The value returned by the function on bits equals the value returned by the function on s.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. n >= 2 and bits[0] = 0. -/
theorem spec_6 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : 2 ≤ n)
    (h0 : bitAt bits.val 0 = some 0) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      Aegis.IsOneBitCharacter.is_one_bit_character (dropSlice bits 1) = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : 2 ≤ n)
    (h0 : bitAt bits.val 0 = some 0), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      Aegis.IsOneBitCharacter.is_one_bit_character (dropSlice bits 1) = ok r) := by
  sorry

/-- Let s be the slice bits[2..n) (indices 2 through n-1). The value returned by the function on bits equals the value returned by the function on s.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. n >= 3 and bits[0] = 1. -/
theorem spec_7 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : 3 ≤ n)
    (h0 : bitAt bits.val 0 = some 1) :
    ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      Aegis.IsOneBitCharacter.is_one_bit_character (dropSlice bits 2) = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hn : 3 ≤ n)
    (h0 : bitAt bits.val 0 = some 1), ∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
      Aegis.IsOneBitCharacter.is_one_bit_character (dropSlice bits 2) = ok r) := by
  sorry

/-- For each c in {[1,0], [1,1]}, let bits' be the concatenation c ++ bits, so len(bits') = n+2, bits'[0] = 1, bits'[1] = c[1], and bits'[i+2] = bits[i] for 0 <= i < n. The value returned by the function on bits' equals the value returned by the function on bits.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. n <= 998. -/
theorem spec_8 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hbound : n ≤ 998) :
    (∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
        Aegis.IsOneBitCharacter.is_one_bit_character
          (consSlice 1#i64 0#i64 bits (by
            have hmax : (1002 : ℕ) ≤ Std.Usize.max := by scalar_tac
            omega)) = ok r) ∧
      (∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
        Aegis.IsOneBitCharacter.is_one_bit_character
          (consSlice 1#i64 1#i64 bits (by
            have hmax : (1002 : ℕ) ≤ Std.Usize.max := by scalar_tac
            omega)) = ok r) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0)
    (hbound : n ≤ 998), (∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
        Aegis.IsOneBitCharacter.is_one_bit_character
          (consSlice 1#i64 0#i64 bits (by
            have hmax : (1002 : ℕ) ≤ Std.Usize.max := by scalar_tac
            omega)) = ok r) ∧
      (∃ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r ∧
        Aegis.IsOneBitCharacter.is_one_bit_character
          (consSlice 1#i64 1#i64 bits (by
            have hmax : (1002 : ℕ) ≤ Std.Usize.max := by scalar_tac
            omega)) = ok r)) := by
  sorry

/-- Whenever the function returns false, n >= 2, bits[n-2] = 1, and in the unique decomposition of bits into blocks [0], [1,0], [1,1], the final block is the two-bit block [1,0] occupying indices n-2 and n-1.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. -/
theorem spec_9 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0) :
    ∀ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r → r = false →
      2 ≤ n ∧ bitAt bits.val (n - 2) = some 1 ∧ EndsWithTwoBitBlock bits.val n := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0), ∀ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r → r = false →
      2 ≤ n ∧ bitAt bits.val (n - 2) = some 1 ∧ EndsWithTwoBitBlock bits.val n) := by
  sorry

/-- Whenever the function returns true, in the unique decomposition of bits into blocks [0], [1,0], [1,1], the final block is the one-bit block [0] occupying index n-1.
  Preconditions: Let n = len(bits). 1 <= n <= 1000. For every i with 0 <= i < n, bits[i] is either 0 or 1. bits[n-1] = 0. -/
theorem spec_10 (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0) :
    ∀ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r → r = true →
      EndsWithOneBitBlock bits.val n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (bits : Slice Std.I64) (n : ℕ)
    (hlen : bits.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 1000)
    (hbits : ∀ i, i < n → bitAt bits.val i = some 0 ∨ bitAt bits.val i = some 1)
    (hlast : bitAt bits.val (n - 1) = some 0), ∀ r, Aegis.IsOneBitCharacter.is_one_bit_character bits = ok r → r = true →
      EndsWithOneBitBlock bits.val n) := by
  sorry

end AegisSpec.IsOneBitCharacter
