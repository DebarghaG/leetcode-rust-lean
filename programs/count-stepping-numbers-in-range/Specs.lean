import Aegis.CountSteppingNumbers.Code.Funs

/-!
# Specifications of `Aegis.CountSteppingNumbers.count_stepping_numbers`

LeetCode problem `count-stepping-numbers-in-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSteppingNumbers

def M : ℤ := 1000000007

def decVal (s : Slice U8) : ℤ :=
  ∑ i : Fin s.val.length, (((s.val[i]).val : ℤ) - 48) * 10 ^ (s.val.length - 1 - i.val)

def decDigitsAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else decDigitsAux fuel (n / 10) ++ [n % 10]

def decDigits (n : ℕ) : List ℕ := decDigitsAux n n

def AdjacentStep (ds : List ℕ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < ds.length),
    ds[i]'(by omega) + 1 = ds[i + 1]'h ∨ ds[i + 1]'h + 1 = ds[i]'(by omega)

def IsStepping (n : ℕ) : Prop := 0 < n ∧ AdjacentStep (decDigits n)

noncomputable def countStepping (lo hi : ℤ) : ℕ := by
  classical
  exact ((Finset.range (hi.toNat + 1)).filter (fun n : ℕ => lo ≤ (n : ℤ) ∧ IsStepping n)).card

def SteppingIn (lo hi n : ℤ) : Prop := lo ≤ n ∧ n ≤ hi ∧ IsStepping n.toNat

def IsCanonicalRep (s : Slice U8) (z : ℤ) : Prop :=
  s.val ≠ [] ∧
    (∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) ∧
      s.val.head? ≠ some 48#u8 ∧ decVal s = z

def one : Slice U8 :=
  ⟨1, Aeneas.Data.ListN.ListN.fromList [49#u8], by
    rw [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> simp [h]⟩

def ValidInput (low high : Slice U8) : Prop :=
  low.val ≠ [] ∧ high.val ≠ [] ∧
    (∀ b ∈ low.val, 48 ≤ b.val ∧ b.val ≤ 57) ∧
      (∀ b ∈ high.val, 48 ≤ b.val ∧ b.val ≤ 57) ∧
        low.val.length ≤ 100 ∧ high.val.length ≤ 100 ∧
          low.val.head? ≠ some 48#u8 ∧ high.val.head? ≠ some 48#u8 ∧
            1 ≤ decVal low ∧ decVal low ≤ decVal high ∧ decVal high < 10 ^ 100

/-- Let M = 1000000007. Call a positive integer n a stepping number if its usual decimal representation d_0 d_1 ... d_{k-1} (with k >= 1, d_0 in {1,...,9}, and each d_i in {0,...,9}) satisfies |d_i - d_{i+1}| = 1 for every 0 <= i < k-1; single-digit positive integers are stepping. Let C be the number of integers n such that val(low) <= n <= val(high) and n is a stepping number. Whenever the function returns a result r, r is the least nonnegative residue of C modulo M, i.e. 0 <= r < M and r is congruent to C modulo M.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_1 (low high : Slice U8) (h : ValidInput low high) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r) :
    0 ≤ r.val ∧ r.val < M ∧
      Int.ModEq M (countStepping (decVal low) (decVal high) : ℤ) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r), 0 ≤ r.val ∧ r.val < M ∧
      Int.ModEq M (countStepping (decVal low) (decVal high) : ℤ) r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; equivalently, it does not fail on these inputs.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_2 (low high : Slice U8) (h : ValidInput low high) :
    ∃ r : I64, Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high), ∃ r : I64, Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < 1000000007.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_3 (low high : Slice U8) (h : ValidInput low high) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r) :
    0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r), 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Let M = 1000000007. Define a stepping number as a positive integer whose usual decimal representation has a nonzero first digit and whose every pair of adjacent digits differs by exactly 1. Let C be the number of stepping numbers n with val(low) <= n <= val(high). If val(high) - val(low) + 1 < M, then the function returns a result r and r = C.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_4 (low high : Slice U8) (h : ValidInput low high)
    (hM : decVal high - decVal low + 1 < M) :
    ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        r.val = (countStepping (decVal low) (decVal high) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high)
    (hM : decVal high - decVal low + 1 < M), ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        r.val = (countStepping (decVal low) (decVal high) : ℤ)) := by
  sorry

/-- Let a stepping number be a positive integer whose usual decimal representation has a nonzero first digit and whose every pair of adjacent digits differs by exactly 1. If val(low) = val(high) = v, then the function returns a result r and r = 1 when v is a stepping number, and r = 0 when v is not a stepping number.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_5 (low high : Slice U8) (h : ValidInput low high) (v : ℤ)
    (hlow : decVal low = v) (hhigh : decVal high = v) :
    ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        (IsStepping v.toNat → r.val = 1) ∧ (¬ IsStepping v.toNat → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (v : ℤ)
    (hlow : decVal low = v) (hhigh : decVal high = v), ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        (IsStepping v.toNat → r.val = 1) ∧ (¬ IsStepping v.toNat → r.val = 0)) := by
  sorry

/-- If val(high) <= 9, then the function returns a result r and r = val(high) - val(low) + 1.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_6 (low high : Slice U8) (h : ValidInput low high) (hhi : decVal high ≤ 9) :
    ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        r.val = decVal high - decVal low + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (hhi : decVal high ≤ 9), ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        r.val = decVal high - decVal low + 1) := by
  sorry

/-- If val(high) = 10 and val(low) <= 10, then the function returns a result r and r = 11 - val(low).
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_7 (low high : Slice U8) (h : ValidInput low high) (hhi : decVal high = 10)
    (hlo : decVal low ≤ 10) :
    ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        r.val = 11 - decVal low := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (hhi : decVal high = 10)
    (hlo : decVal low ≤ 10), ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧
        r.val = 11 - decVal low) := by
  sorry

/-- Let M = 1000000007. For any integer x with val(low) <= x < val(high), let mid be the standard decimal representation of x with no leading zeros, and let next be the standard decimal representation of x+1 with no leading zeros. If the function returns r for (low, high), r1 for (low, mid), and r2 for (next, high), then r is congruent to r1 + r2 modulo M.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_8 (low high : Slice U8) (h : ValidInput low high) (x : ℤ)
    (hx : decVal low ≤ x ∧ x < decVal high) (mid next : Slice U8)
    (hmid : IsCanonicalRep mid x) (hnext : IsCanonicalRep next (x + 1)) (r r1 r2 : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (hr1 : Aegis.CountSteppingNumbers.count_stepping_numbers low mid = ok r1)
    (hr2 : Aegis.CountSteppingNumbers.count_stepping_numbers next high = ok r2) :
    Int.ModEq M (r1.val + r2.val) r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (x : ℤ)
    (hx : decVal low ≤ x ∧ x < decVal high) (mid next : Slice U8)
    (hmid : IsCanonicalRep mid x) (hnext : IsCanonicalRep next (x + 1)) (r r1 r2 : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (hr1 : Aegis.CountSteppingNumbers.count_stepping_numbers low mid = ok r1)
    (hr2 : Aegis.CountSteppingNumbers.count_stepping_numbers next high = ok r2), Int.ModEq M (r1.val + r2.val) r.val) := by
  sorry

/-- Let M = 1000000007. Let one be the one-byte slice whose only byte is 49 (the ASCII digit 1). If val(low) > 1, let prev be the byte slice of ASCII decimal digits giving the standard decimal representation of val(low)-1 with no leading zeros. If the function returns r for (low, high), a for (one, high), and b for (one, prev), then r is congruent to a - b modulo M.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_9 (low high : Slice U8) (h : ValidInput low high) (hgt : 1 < decVal low)
    (prev : Slice U8) (hprev : IsCanonicalRep prev (decVal low - 1)) (r a b : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (ha : Aegis.CountSteppingNumbers.count_stepping_numbers one high = ok a)
    (hb : Aegis.CountSteppingNumbers.count_stepping_numbers one prev = ok b) :
    Int.ModEq M (a.val - b.val) r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high) (hgt : 1 < decVal low)
    (prev : Slice U8) (hprev : IsCanonicalRep prev (decVal low - 1)) (r a b : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (ha : Aegis.CountSteppingNumbers.count_stepping_numbers one high = ok a)
    (hb : Aegis.CountSteppingNumbers.count_stepping_numbers one prev = ok b), Int.ModEq M (a.val - b.val) r.val) := by
  sorry

/-- Let M = 1000000007. Define a stepping number as a positive integer whose usual decimal representation has a nonzero first digit and whose every pair of adjacent digits differs by exactly 1. If val(high) - val(low) + 1 < M and the function returns a result r with r != 0, then there exists an integer n such that val(low) <= n <= val(high) and n is a stepping number.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_10 (low high : Slice U8) (h : ValidInput low high)
    (hM : decVal high - decVal low + 1 < M) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (hne : r.val ≠ 0) : ∃ n : ℤ, SteppingIn (decVal low) (decVal high) n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high)
    (hM : decVal high - decVal low + 1 < M) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (hne : r.val ≠ 0), ∃ n : ℤ, SteppingIn (decVal low) (decVal high) n) := by
  sorry

/-- Let M = 1000000007. Define a stepping number as a positive integer whose usual decimal representation has a nonzero first digit and whose every pair of adjacent digits differs by exactly 1. If val(high) - val(low) + 1 < M and the function returns a result r with r = 0, then there is no integer n such that val(low) <= n <= val(high) and n is a stepping number.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_11 (low high : Slice U8) (h : ValidInput low high)
    (hM : decVal high - decVal low + 1 < M) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (hz : r.val = 0) : ¬ ∃ n : ℤ, SteppingIn (decVal low) (decVal high) n := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high)
    (hM : decVal high - decVal low + 1 < M) (r : I64)
    (hr : Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r)
    (hz : r.val = 0), ¬ ∃ n : ℤ, SteppingIn (decVal low) (decVal high) n) := by
  sorry

/-- Define a stepping number as a positive integer whose usual decimal representation has a nonzero first digit and whose every pair of adjacent digits differs by exactly 1. If there is no integer n such that val(low) <= n <= val(high) and n is a stepping number, then the function returns a result r and r = 0.
  Preconditions: low and high are non-empty byte slices of ASCII decimal digits (for every i with 0 <= i < len(low), 48 <= low[i] <= 57, and similarly for high); len(low) <= 100 and len(high) <= 100; low[0] != 48 and high[0] != 48; val(low) >= 1; val(low) <= val(high); val(high) < 10^100, where val(s) = sum_{i=0}^{len(s)-1} (s[i]-48) * 10^(len(s)-1-i). -/
theorem spec_12 (low high : Slice U8) (h : ValidInput low high)
    (hnone : ¬ ∃ n : ℤ, SteppingIn (decVal low) (decVal high) n) :
    ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧ r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (low high : Slice U8) (h : ValidInput low high)
    (hnone : ¬ ∃ n : ℤ, SteppingIn (decVal low) (decVal high) n), ∃ r : I64,
      Aegis.CountSteppingNumbers.count_stepping_numbers low high = ok r ∧ r.val = 0) := by
  sorry

end AegisSpec.CountSteppingNumbers
