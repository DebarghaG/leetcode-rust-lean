import Aegis.MinSwaps.Code.Funs

/-!
# Specifications of `Aegis.MinSwaps.min_swaps`

LeetCode problem `minimum-number-of-swaps-to-make-the-binary-string-alternating`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinSwaps

def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def bLen (s : Slice Std.U8) : Nat := s.val.length

def countOf (l : List Nat) (b : Nat) : Nat := (l.filter (fun x => x = b)).length

def byteAt (l : List Nat) (i : Nat) : Nat := (l[i]?).getD 0

def hamming (l t : List Nat) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => byteAt l i ≠ byteAt t i)).length

def countEvenAt (l : List Nat) (n b : Nat) : Nat :=
  ((List.range n).filter (fun i => i % 2 = 0 ∧ byteAt l i = b)).length

def altWord (first n : Nat) : List Nat :=
  (List.range n).map (fun i => if i % 2 = 0 then first else 97 - first)

def IsAlternating (l : List Nat) : Prop :=
  ∀ i, i + 1 < l.length → byteAt l i ≠ byteAt l (i + 1)

def IsAltWordOfLen (t : List Nat) (n : Nat) : Prop := t = altWord 48 n ∨ t = altWord 49 n

def feasible (l : List Nat) (n p : Nat) : Prop := countOf (altWord p n) 48 = countOf l 48

def cost (l : List Nat) (n p : Nat) : Nat := hamming l (altWord p n) n / 2

def zerosCount (s : Slice Std.U8) : Nat := countOf (bytes s) 48

def onesCount (s : Slice Std.U8) : Nat := bLen s - zerosCount s

def imbalance (s : Slice Std.U8) : Int := (zerosCount s : Int) - (onesCount s : Int)

def flipBit (b : Nat) : Nat := if b = 48 then 49 else 48

def ValidInput (s : Slice Std.U8) : Prop :=
  1 ≤ bLen s ∧ bLen s ≤ 1000 ∧
    ∀ i, i < bLen s → byteAt (bytes s) i = 48 ∨ byteAt (bytes s) i = 49

/-- Let z = #{i | 0 <= i < n and s[i] = 48} and o = n - z. For p in {0,1}, define the alternating string T_p of length n by: T_0[i] = 48 if i is even and T_0[i] = 49 if i is odd; T_1[i] = 49 if i is even and T_1[i] = 48 if i is odd. Call p feasible when #{i | 0 <= i < n and T_p[i] = 48} = z. Let D_p = #{i | 0 <= i < n and s[i] != T_p[i]} for feasible p. The function returns a result r and: (a) if no p is feasible, then r = -1; (b) if some p is feasible, then r = min{ D_p/2 | p is feasible }, where D_p/2 is the integer value (D_p is even for every feasible p).
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). All indices are 0-based. -/
theorem spec_1 (s : Slice Std.U8) (h : ValidInput s) :
    ∃ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r ∧
        (¬ (feasible (bytes s) (bLen s) 48 ∨ feasible (bytes s) (bLen s) 49) → r.val = -1) ∧
        ((feasible (bytes s) (bLen s) 48 ∨ feasible (bytes s) (bLen s) 49) →
          (∃ p : Nat,
              (p = 48 ∨ p = 49) ∧
                feasible (bytes s) (bLen s) p ∧
                r.val = ((cost (bytes s) (bLen s) p : Nat) : Int)) ∧
            (∀ q : Nat,
              (q = 48 ∨ q = 49) →
                feasible (bytes s) (bLen s) q →
                  r.val ≤ ((cost (bytes s) (bLen s) q : Nat) : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∃ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r ∧
        (¬ (feasible (bytes s) (bLen s) 48 ∨ feasible (bytes s) (bLen s) 49) → r.val = -1) ∧
        ((feasible (bytes s) (bLen s) 48 ∨ feasible (bytes s) (bLen s) 49) →
          (∃ p : Nat,
              (p = 48 ∨ p = 49) ∧
                feasible (bytes s) (bLen s) p ∧
                r.val = ((cost (bytes s) (bLen s) p : Nat) : Int)) ∧
            (∀ q : Nat,
              (q = 48 ∨ q = 49) →
                feasible (bytes s) (bLen s) q →
                  r.val ≤ ((cost (bytes s) (bLen s) q : Nat) : Int)))) := by
  sorry

/-- The function returns a result r (i.e. min_swaps(s) = Result.ok r); in particular it does not panic, access out of bounds, or overflow for any input satisfying the preconditions.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. -/
theorem spec_2 (s : Slice Std.U8) (h : ValidInput s) :
    ∃ r : Std.I64, Aegis.MinSwaps.min_swaps s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∃ r : Std.I64, Aegis.MinSwaps.min_swaps s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if no alternating byte string t of length n has the same number of occurrences of byte 48 ('0') as s. Equivalently, r = -1 if and only if |z - o| > 1, where z = #{i | 0 <= i < n and s[i] = 48} and o = n - z.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. -/
theorem spec_3 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        (r.val = -1 ↔
            ¬ ∃ t : List Nat,
              IsAltWordOfLen t (bLen s) ∧ countOf t 48 = zerosCount s) ∧
          (r.val = -1 ↔ 1 < (imbalance s).natAbs) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        (r.val = -1 ↔
            ¬ ∃ t : List Nat,
              IsAltWordOfLen t (bLen s) ∧ countOf t 48 = zerosCount s) ∧
          (r.val = -1 ↔ 1 < (imbalance s).natAbs)) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then 0 <= r <= floor(n/2). In particular, since n <= 1000, every nonnegative result is at most 500.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. -/
theorem spec_4 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val ≠ -1 →
          0 ≤ r.val ∧ r.val ≤ ((bLen s / 2 : Nat) : Int) ∧ r.val ≤ 500 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val ≠ -1 →
          0 ≤ r.val ∧ r.val ≤ ((bLen s / 2 : Nat) : Int) ∧ r.val ≤ 500) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every alternating byte string t of length n such that #{i | 0 <= i < n and t[i] = 48} = z, the Hamming distance D(s,t) = #{i | 0 <= i < n and s[i] != t[i]} satisfies D(s,t) >= 2*r.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. Let z = #{i | 0 <= i < n and s[i] = 48}. -/
theorem spec_5 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        0 ≤ r.val →
          ∀ t : List Nat,
            IsAltWordOfLen t (bLen s) →
              countOf t 48 = zerosCount s →
                (hamming (bytes s) t (bLen s) : Int) ≥ 2 * r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        0 ≤ r.val →
          ∀ t : List Nat,
            IsAltWordOfLen t (bLen s) →
              countOf t 48 = zerosCount s →
                (hamming (bytes s) t (bLen s) : Int) ≥ 2 * r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists an alternating byte string t of length n such that #{i | 0 <= i < n and t[i] = 48} = z and D(s,t) = #{i | 0 <= i < n and s[i] != t[i]} = 2*r.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. Let z = #{i | 0 <= i < n and s[i] = 48}. -/
theorem spec_6 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        0 ≤ r.val →
          ∃ t : List Nat,
            IsAltWordOfLen t (bLen s) ∧
              countOf t 48 = zerosCount s ∧
                (hamming (bytes s) t (bLen s) : Int) = 2 * r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        0 ≤ r.val →
          ∃ t : List Nat,
            IsAltWordOfLen t (bLen s) ∧
              countOf t 48 = zerosCount s ∧
                (hamming (bytes s) t (bLen s) : Int) = 2 * r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < n-1, s[i] != s[i+1] (that is, s itself is already alternating).
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. -/
theorem spec_7 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r → (r.val = 0 ↔ IsAlternating (bytes s)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r → (r.val = 0 ↔ IsAlternating (bytes s))) := by
  sorry

/-- Whenever the function returns a result r, r = #{i | 0 <= i < n, i is even, and s[i] = 49}, the number of 0-based even positions containing '1'.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. Also assume n is odd and z = (n+1)/2, where z = #{i | 0 <= i < n and s[i] = 48}; equivalently, s has one more '0' than '1'. -/
theorem spec_8 (s : Slice Std.U8) (h : ValidInput s)
    (hodd : bLen s % 2 = 1) (hz : zerosCount s = (bLen s + 1) / 2) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val = ((countEvenAt (bytes s) (bLen s) 49 : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s)
    (hodd : bLen s % 2 = 1) (hz : zerosCount s = (bLen s + 1) / 2), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val = ((countEvenAt (bytes s) (bLen s) 49 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = #{i | 0 <= i < n, i is even, and s[i] = 48}, the number of 0-based even positions containing '0'.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. Also assume n is odd and o = (n+1)/2, where o = #{i | 0 <= i < n and s[i] = 49}; equivalently, s has one more '1' than '0'. -/
theorem spec_9 (s : Slice Std.U8) (h : ValidInput s)
    (hodd : bLen s % 2 = 1) (ho : onesCount s = (bLen s + 1) / 2) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val = ((countEvenAt (bytes s) (bLen s) 48 : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s)
    (hodd : bLen s % 2 = 1) (ho : onesCount s = (bLen s + 1) / 2), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val = ((countEvenAt (bytes s) (bLen s) 48 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = min(E1, E0), where E1 = #{i | 0 <= i < n, i is even, and s[i] = 49} and E0 = #{i | 0 <= i < n, i is even, and s[i] = 48}.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. Also assume n is even and z = n/2, where z = #{i | 0 <= i < n and s[i] = 48}; equivalently, s has equally many '0's and '1's. -/
theorem spec_10 (s : Slice Std.U8) (h : ValidInput s)
    (heven : bLen s % 2 = 0) (hz : zerosCount s = bLen s / 2) :
    ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val = ((min (countEvenAt (bytes s) (bLen s) 49) (countEvenAt (bytes s) (bLen s) 48)
            : Nat) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s)
    (heven : bLen s % 2 = 0) (hz : zerosCount s = bLen s / 2), ∀ r : Std.I64,
      Aegis.MinSwaps.min_swaps s = ok r →
        r.val = ((min (countEvenAt (bytes s) (bLen s) 49) (countEvenAt (bytes s) (bLen s) 48)
            : Nat) : Int)) := by
  sorry

/-- Let complement(s) be the byte string of length n with complement(s)[i] = 49 if s[i] = 48, and complement(s)[i] = 48 if s[i] = 49. If min_swaps(s) returns r and min_swaps(complement(s)) returns r', then r = r'.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. -/
theorem spec_11 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ (t : Slice Std.U8), bytes t = (bytes s).map flipBit →
      ∀ r r' : Std.I64,
        Aegis.MinSwaps.min_swaps s = ok r →
          Aegis.MinSwaps.min_swaps t = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ (t : Slice Std.U8), bytes t = (bytes s).map flipBit →
      ∀ r r' : Std.I64,
        Aegis.MinSwaps.min_swaps s = ok r →
          Aegis.MinSwaps.min_swaps t = ok r' → r.val = r'.val) := by
  sorry

/-- Let rev(s) be the byte string of length n with rev(s)[i] = s[n-1-i] for 0 <= i < n. If min_swaps(s) returns r and min_swaps(rev(s)) returns r', then r = r'.
  Preconditions: Let n = len(s). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, s[i] is either 48 or 49. -/
theorem spec_12 (s : Slice Std.U8) (h : ValidInput s) :
    ∀ (t : Slice Std.U8), bytes t = (bytes s).reverse →
      ∀ r r' : Std.I64,
        Aegis.MinSwaps.min_swaps s = ok r →
          Aegis.MinSwaps.min_swaps t = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (h : ValidInput s), ∀ (t : Slice Std.U8), bytes t = (bytes s).reverse →
      ∀ r r' : Std.I64,
        Aegis.MinSwaps.min_swaps s = ok r →
          Aegis.MinSwaps.min_swaps t = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.MinSwaps
