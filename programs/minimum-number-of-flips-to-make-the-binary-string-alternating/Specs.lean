import Aegis.MinFlips.Code.Funs

/-!
# Specifications of `Aegis.MinFlips.min_flips`

LeetCode problem `minimum-number-of-flips-to-make-the-binary-string-alternating`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinFlips

namespace AegisSpec.MinFlips

def slen (s : Slice U8) : Nat := s.val.length

def byteAt (s : Slice U8) (i : Nat) : Nat := (s.val[i]?).elim 0 (fun b => b.val)

def A0 (i : Nat) : Nat := if i % 2 = 0 then 48 else 49

def A1 (i : Nat) : Nat := if i % 2 = 0 then 49 else 48

def rotAt (s : Slice U8) (m i : Nat) : Nat := byteAt s ((i + m) % slen s)

def mismCount (s : Slice U8) (T : Nat → Nat) (m : Nat) : Nat :=
  ((Finset.range (slen s)).filter (fun i => rotAt s m i ≠ T i)).card

def mismCountId (s : Slice U8) (T : Nat → Nat) : Nat :=
  ((Finset.range (slen s)).filter (fun i => byteAt s i ≠ T i)).card

def d (s : Slice U8) (m : Nat) : Nat :=
  min (mismCount s A0 m) (mismCount s A1 m)

def dmin (s : Slice U8) : Nat :=
  if h : (Finset.range (slen s)).Nonempty then (Finset.range (slen s)).inf' h (d s) else 0

/-- Let n = len(s). For each m with 0 <= m < n and each i with 0 <= i < n, let R_m(i) = s[(i + m) mod n]. Let A0(i) = 48 if i is even and 49 if i is odd, and let A1(i) = 49 if i is even and 48 if i is odd. For each m, let d(m) be the minimum of the two counts: the number of i with 0 <= i < n and R_m(i) != A0(i), and the number of i with 0 <= i < n and R_m(i) != A1(i). The function returns a result r and r = min over m with 0 <= m < n of d(m).
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_1 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∃ r : I64, min_flips s = ok r ∧ r.val = (dmin s : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∃ r : I64, min_flips s = ok r ∧ r.val = (dmin s : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_2 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∃ r : I64, min_flips s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∃ r : I64, min_flips s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_3 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∀ r : I64, min_flips s = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : I64, min_flips s = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= floor(len(s)/2).
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_4 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∀ r : I64, min_flips s = ok r → r.val ≤ ((slen s / 2 : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : I64, min_flips s = ok r → r.val ≤ ((slen s / 2 : Nat) : Int)) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, r = 0 if and only if there exists m with 0 <= m < n such that for every i with 0 <= i < n - 1, s[(i + m) mod n] != s[(i + 1 + m) mod n].
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_5 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∀ r : I64, min_flips s = ok r →
      (r.val = 0 ↔
        ∃ m, m < slen s ∧
          ∀ i, i + 1 < slen s →
            byteAt s ((i + m) % slen s) ≠ byteAt s ((i + 1 + m) % slen s)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : I64, min_flips s = ok r →
      (r.val = 0 ↔
        ∃ m, m < slen s ∧
          ∀ i, i + 1 < slen s →
            byteAt s ((i + m) % slen s) ≠ byteAt s ((i + 1 + m) % slen s))) := by
  sorry

/-- Whenever the function returns a result r, r = floor(len(s)/2).
  Preconditions: len(s) >= 2; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'; and for every i, j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j]. -/
theorem spec_6 (s : Slice U8)
    (hlen : 2 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49)
    (hconst : ∀ i j, i < slen s → j < slen s → byteAt s i = byteAt s j) :
    ∀ r : I64, min_flips s = ok r → r.val = ((slen s / 2 : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 2 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49)
    (hconst : ∀ i j, i < slen s → j < slen s → byteAt s i = byteAt s j), ∀ r : I64, min_flips s = ok r → r.val = ((slen s / 2 : Nat) : Int)) := by
  sorry

/-- Let n = len(s). Let A0(i) = 48 if i is even and 49 if i is odd, for 0 <= i < n. Let c0 be the number of i with 0 <= i < n and s[i] != A0(i). Whenever the function returns a result r, r <= min(c0, n - c0).
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_7 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∀ r : I64, min_flips s = ok r →
      r.val ≤ ((min (mismCountId s A0) (slen s - mismCountId s A0) : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : I64, min_flips s = ok r →
      r.val ≤ ((min (mismCountId s A0) (slen s - mismCountId s A0) : Nat) : Int)) := by
  sorry

/-- Let n = len(s), and define R_m(i) = s[(i + m) mod n] for 0 <= m < n and 0 <= i < n. Let A0(i) = 48 if i is even and 49 if i is odd, and let A1(i) = 49 if i is even and 48 if i is odd. Whenever the function returns a result r, there exist m with 0 <= m < n and T in {A0, A1} such that the number of i with 0 <= i < n and R_m(i) != T(i) is exactly r.
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_8 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∀ r : I64, min_flips s = ok r →
      ∃ m, m < slen s ∧
        ((mismCount s A0 m : Nat) : Int) = r.val ∨
        ((mismCount s A1 m : Nat) : Int) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : I64, min_flips s = ok r →
      ∃ m, m < slen s ∧
        ((mismCount s A0 m : Nat) : Int) = r.val ∨
        ((mismCount s A1 m : Nat) : Int) = r.val) := by
  sorry

/-- Let n = len(s), and define R_m(i) = s[(i + m) mod n] for 0 <= m < n and 0 <= i < n. Let A0(i) = 48 if i is even and 49 if i is odd, and let A1(i) = 49 if i is even and 48 if i is odd. Whenever the function returns a result r, for every m with 0 <= m < n and every T in {A0, A1}, the number of i with 0 <= i < n and R_m(i) != T(i) is at least r.
  Preconditions: len(s) >= 1; len(s) <= 100000; and for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'. -/
theorem spec_9 (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49) :
    ∀ r : I64, min_flips s = ok r →
      ∀ m, m < slen s →
        ∀ T : Nat → Nat, (T = A0 ∨ T = A1) → r.val ≤ ((mismCount s T m : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : I64, min_flips s = ok r →
      ∀ m, m < slen s →
        ∀ T : Nat → Nat, (T = A0 ∨ T = A1) → r.val ≤ ((mismCount s T m : Nat) : Int)) := by
  sorry

/-- Whenever min_flips(s) returns a result r and min_flips(t) returns a result r_t, we have r_t = r.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] is ASCII '0' or ASCII '1'; and for some m with 0 <= m < len(s), t is a sequence of length len(s) satisfying t[i] = s[(i + m) mod len(s)] for every i with 0 <= i < len(s). -/
theorem spec_10 (s t : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49)
    (hrot : ∃ m, m < slen s ∧ slen t = slen s ∧
      ∀ i, i < slen s → byteAt t i = byteAt s ((i + m) % slen s)) :
    ∀ r rt : I64, min_flips s = ok r → min_flips t = ok rt → rt = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen : 1 ≤ slen s) (hlen_le : slen s ≤ 100000)
    (hbits : ∀ i, i < slen s → byteAt s i = 48 ∨ byteAt s i = 49)
    (hrot : ∃ m, m < slen s ∧ slen t = slen s ∧
      ∀ i, i < slen s → byteAt t i = byteAt s ((i + m) % slen s)), ∀ r rt : I64, min_flips s = ok r → min_flips t = ok rt → rt = r) := by
  sorry

end AegisSpec.MinFlips
