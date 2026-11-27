import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `number-of-ways-to-select-buildings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std

def Slice.bytes (s : Slice Std.U8) : List ℕ := s.list.toList.map (fun b => b.val)

def Slice.byte (s : Slice Std.U8) (i : ℕ) : ℕ := s.bytes.getD i 0

theorem Slice.bytes_length (s : Slice Std.U8) : s.bytes.length = s.leng := by
  simp [Slice.bytes, Aeneas.Data.ListN.ListN_length]

end Aeneas.Std

namespace AegisSpec.NumberOfWays

def isBit (b : ℕ) : Prop := b = 48 ∨ b = 49

def ValidInput (s : Slice Std.U8) : Prop :=
  3 ≤ s.bytes.length ∧ s.bytes.length ≤ 100000 ∧ ∀ b ∈ s.bytes, isBit b

def tripleBound (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

def numTriples (s : Slice Std.U8) (P : ℕ → ℕ → ℕ → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin s.bytes.length × Fin s.bytes.length × Fin s.bytes.length)).filter
      (fun t => t.1.val < t.2.1.val ∧ t.2.1.val < t.2.2.val ∧
        P (s.byte t.1.val) (s.byte t.2.1.val) (s.byte t.2.2.val) = true)).card

def validTriples (s : Slice Std.U8) : ℕ :=
  numTriples s (fun a b c => a != b && b != c)

def count010 (s : Slice Std.U8) : ℕ :=
  numTriples s (fun a b c => a == 48 && b == 49 && c == 48)

def count101 (s : Slice Std.U8) : ℕ :=
  numTriples s (fun a b c => a == 49 && b == 48 && c == 49)

def leftCount (s : Slice Std.U8) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => s.byte i ≠ s.byte j)).card

def rightCount (s : Slice Std.U8) (j : ℕ) : ℕ :=
  ((Finset.Ioo j s.bytes.length).filter (fun k => s.byte k ≠ s.byte j)).card

def middleCount (s : Slice Std.U8) (j : ℕ) : ℕ :=
  (((Finset.range j).product (Finset.Ioo j s.bytes.length)).filter
      (fun p => s.byte p.1 ≠ s.byte j ∧ s.byte p.2 ≠ s.byte j)).card

def flipByte (b : ℕ) : ℕ := if b = 48 then 49 else 48

def flipBytes (s : Slice Std.U8) : List ℕ := s.bytes.map flipByte

def revBytes (s : Slice Std.U8) : List ℕ := s.bytes.reverse

def IsZeroThenOne (s : Slice Std.U8) : Prop :=
  ∃ p, p ≤ s.bytes.length ∧ (∀ i, i < p → s.byte i = 48) ∧
    (∀ i, p ≤ i → i < s.bytes.length → s.byte i = 49)

def IsOneThenZero (s : Slice Std.U8) : Prop :=
  ∃ p, p ≤ s.bytes.length ∧ (∀ i, i < p → s.byte i = 49) ∧
    (∀ i, p ≤ i → i < s.bytes.length → s.byte i = 48)

def AdjacentTypesDiffer (runs : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ runs.zip runs.tail, p.1.1 ≠ p.2.1

def IsRunDecomposition (s : Slice Std.U8) (runs : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ runs, isBit p.1 ∧ 0 < p.2) ∧
  AdjacentTypesDiffer runs ∧
  s.bytes = (runs.map (fun p : ℕ × ℕ => List.replicate p.2 p.1)).flatten

def runTripleSum (runs : List (ℕ × ℕ)) : ℕ :=
  ((Finset.univ : Finset (Fin runs.length × Fin runs.length × Fin runs.length)).filter
      (fun t => t.1.val < t.2.1.val ∧ t.2.1.val < t.2.2.val ∧
        (runs.get t.1).1 ≠ (runs.get t.2.1).1 ∧
        (runs.get t.2.1).1 ≠ (runs.get t.2.2).1)).sum
    (fun t => (runs.get t.1).2 * (runs.get t.2.1).2 * (runs.get t.2.2).2)

def betweenCount (s : Slice Std.U8) (i k : ℕ) : ℕ :=
  ((Finset.Ioo i k).filter (fun j => s.byte j ≠ s.byte i)).card

def equalPairSum (s : Slice Std.U8) : ℕ :=
  ((Finset.univ : Finset (Fin s.bytes.length × Fin s.bytes.length)).filter
      (fun p => p.1.val < p.2.val ∧ s.byte p.1.val = s.byte p.2.val)).sum
    (fun p => betweenCount s p.1.val p.2.val)

/-- The function returns a result r, and r equals the number of triples (i, j, k) of indices such that 0 <= i < j < k < len(s), s[i] != s[j], and s[j] != s[k]. Equivalently, r is the number of ways to choose three distinct buildings whose types, in increasing index order, are either 0,1,0 or 1,0,1.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_1 (s : Slice Std.U8) (hs : ValidInput s) :
    ∃ r, Aegis.NumberOfWays.number_of_ways s = ok r ∧ r.val = (validTriples s : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∃ r, Aegis.NumberOfWays.number_of_ways s = ok r ∧ r.val = (validTriples s : ℤ)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, access out of bounds, or overflow the I64 result. In particular, r is at most len(s)*(len(s)-1)*(len(s)-2)/6, which for len(s) <= 100000 is less than 2^63.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_2 (s : Slice Std.U8) (hs : ValidInput s) :
    ∃ r, Aegis.NumberOfWays.number_of_ways s = ok r ∧ 0 ≤ r.val ∧
      r.val ≤ (tripleBound s.bytes.length : ℤ) ∧ tripleBound s.bytes.length < 2 ^ 63 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∃ r, Aegis.NumberOfWays.number_of_ways s = ok r ∧ 0 ≤ r.val ∧
      r.val ≤ (tripleBound s.bytes.length : ℤ) ∧ tripleBound s.bytes.length < 2 ^ 63) := by
  sorry

/-- The returned value r satisfies 0 <= r <= len(s) * (len(s) - 1) * (len(s) - 2) / 6.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_3 (s : Slice Std.U8) (hs : ValidInput s) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      0 ≤ r.val ∧ r.val ≤ (tripleBound s.bytes.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      0 ≤ r.val ∧ r.val ≤ (tripleBound s.bytes.length : ℤ)) := by
  sorry

/-- The returned value r is 0 if and only if s is nondecreasing or nonincreasing as a byte sequence: either there exists p with 0 <= p <= len(s) such that s[i] = 48 for all i < p and s[i] = 49 for all i >= p, or there exists p with 0 <= p <= len(s) such that s[i] = 49 for all i < p and s[i] = 48 for all i >= p.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_4 (s : Slice Std.U8) (hs : ValidInput s) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      (r.val = 0 ↔ IsZeroThenOne s ∨ IsOneThenZero s) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      (r.val = 0 ↔ IsZeroThenOne s ∨ IsOneThenZero s)) := by
  sorry

/-- Let A be the number of triples i < j < k with s[i] = 48, s[j] = 49, and s[k] = 48. Let B be the number of triples i < j < k with s[i] = 49, s[j] = 48, and s[k] = 49. Then r = A + B.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_5 (s : Slice Std.U8) (hs : ValidInput s) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      r.val = ((count010 s + count101 s : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      r.val = ((count010 s + count101 s : ℕ) : ℤ)) := by
  sorry

/-- For every index j with 1 <= j <= len(s)-2, let L(j) be the number of indices i with 0 <= i < j and s[i] != s[j], and let R(j) be the number of indices k with j < k < len(s) and s[k] != s[j]. Then the number of valid triples whose middle selected index is j is exactly L(j) * R(j). In particular, summing these contributions over all such j gives r.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_6 (s : Slice Std.U8) (hs : ValidInput s) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      (∀ j, 1 ≤ j → j ≤ s.bytes.length - 2 →
        middleCount s j = leftCount s j * rightCount s j) ∧
      r.val = ((Finset.range s.bytes.length).sum (fun j => middleCount s j) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r →
      (∀ j, 1 ≤ j → j ≤ s.bytes.length - 2 →
        middleCount s j = leftCount s j * rightCount s j) ∧
      r.val = ((Finset.range s.bytes.length).sum (fun j => middleCount s j) : ℤ)) := by
  sorry

/-- Let t be any byte slice with len(t) = len(s) such that, for every i with 0 <= i < len(s), t[i] = 49 if s[i] = 48 and t[i] = 48 if s[i] = 49. If r is the result for s and r' is the result for t, then r = r'.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_7 (s t : Slice Std.U8) (hs : ValidInput s)
    (hlen : t.bytes.length = s.bytes.length) (hflip : t.bytes = flipBytes s) :
    ∀ r r', Aegis.NumberOfWays.number_of_ways s = ok r →
      Aegis.NumberOfWays.number_of_ways t = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : ValidInput s)
    (hlen : t.bytes.length = s.bytes.length) (hflip : t.bytes = flipBytes s), ∀ r r', Aegis.NumberOfWays.number_of_ways s = ok r →
      Aegis.NumberOfWays.number_of_ways t = ok r' → r = r') := by
  sorry

/-- Let t be the byte slice with len(t) = len(s) and t[i] = s[len(s)-1-i] for every 0 <= i < len(s). If r is the result for s and r' is the result for t, then r = r'.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_8 (s t : Slice Std.U8) (hs : ValidInput s)
    (hlen : t.bytes.length = s.bytes.length) (hrev : t.bytes = revBytes s) :
    ∀ r r', Aegis.NumberOfWays.number_of_ways s = ok r →
      Aegis.NumberOfWays.number_of_ways t = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : ValidInput s)
    (hlen : t.bytes.length = s.bytes.length) (hrev : t.bytes = revBytes s), ∀ r r', Aegis.NumberOfWays.number_of_ways s = ok r →
      Aegis.NumberOfWays.number_of_ways t = ok r' → r = r') := by
  sorry

/-- Let t be any byte slice whose bytes are all 48 or 49, with len(s) + len(t) <= 100000, and let u be the concatenation of s followed by t, so u[i] = s[i] for 0 <= i < len(s) and u[len(s)+i] = t[i] for 0 <= i < len(t). If r is the result for s and r_u is the result for u, then r <= r_u.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_9 (s t u : Slice Std.U8) (hs : ValidInput s)
    (hbits : ∀ b ∈ t.bytes, isBit b)
    (hlen : s.bytes.length + t.bytes.length ≤ 100000)
    (hcat : u.bytes = s.bytes ++ t.bytes) :
    ∀ r r_u, Aegis.NumberOfWays.number_of_ways s = ok r →
      Aegis.NumberOfWays.number_of_ways u = ok r_u → r.val ≤ r_u.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t u : Slice Std.U8) (hs : ValidInput s)
    (hbits : ∀ b ∈ t.bytes, isBit b)
    (hlen : s.bytes.length + t.bytes.length ≤ 100000)
    (hcat : u.bytes = s.bytes ++ t.bytes), ∀ r r_u, Aegis.NumberOfWays.number_of_ways s = ok r →
      Aegis.NumberOfWays.number_of_ways u = ok r_u → r.val ≤ r_u.val) := by
  sorry

/-- If s has exactly three maximal constant runs, i.e., if there exist positive integers a, b, c with a+b+c = len(s) such that either (s[i] = 48 for 0 <= i < a, s[i] = 49 for a <= i < a+b, and s[i] = 48 for a+b <= i < len(s)) or (s[i] = 49 for 0 <= i < a, s[i] = 48 for a <= i < a+b, and s[i] = 49 for a+b <= i < len(s)), then r = a * b * c.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_10 (s : Slice Std.U8) (hs : ValidInput s) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hlen : a + b + c = s.bytes.length)
    (hruns : ((∀ i, i < a → s.byte i = 48) ∧
          (∀ i, a ≤ i → i < a + b → s.byte i = 49) ∧
          (∀ i, a + b ≤ i → i < s.bytes.length → s.byte i = 48)) ∨
        ((∀ i, i < a → s.byte i = 49) ∧
          (∀ i, a ≤ i → i < a + b → s.byte i = 48) ∧
          (∀ i, a + b ≤ i → i < s.bytes.length → s.byte i = 49))) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r → r.val = ((a * b * c : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hlen : a + b + c = s.bytes.length)
    (hruns : ((∀ i, i < a → s.byte i = 48) ∧
          (∀ i, a ≤ i → i < a + b → s.byte i = 49) ∧
          (∀ i, a + b ≤ i → i < s.bytes.length → s.byte i = 48)) ∨
        ((∀ i, i < a → s.byte i = 49) ∧
          (∀ i, a ≤ i → i < a + b → s.byte i = 48) ∧
          (∀ i, a + b ≤ i → i < s.bytes.length → s.byte i = 49))), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r → r.val = ((a * b * c : ℕ) : ℤ)) := by
  sorry

/-- Let the maximal constant runs of s have lengths L_0, ..., L_{m-1} and types c_0, ..., c_{m-1} in {48,49}, so c_{r+1} != c_r for all 0 <= r < m-1. Then r = sum over all 0 <= p < q < t < m with c_p != c_q and c_q != c_t of L_p * L_q * L_t.
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_11 (s : Slice Std.U8) (hs : ValidInput s) (runs : List (ℕ × ℕ))
    (hruns : IsRunDecomposition s runs) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r → r.val = (runTripleSum runs : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (runs : List (ℕ × ℕ))
    (hruns : IsRunDecomposition s runs), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r → r.val = (runTripleSum runs : ℤ)) := by
  sorry

/-- For every pair of indices i < k with s[i] = s[k], let M(i,k) be the number of indices j with i < j < k and s[j] != s[i]. Then r = sum over all such pairs (i,k) of M(i,k).
  Preconditions: 3 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_12 (s : Slice Std.U8) (hs : ValidInput s) :
    ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r → r.val = (equalPairSum s : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∀ r, Aegis.NumberOfWays.number_of_ways s = ok r → r.val = (equalPairSum s : ℤ)) := by
  sorry

end AegisSpec.NumberOfWays
