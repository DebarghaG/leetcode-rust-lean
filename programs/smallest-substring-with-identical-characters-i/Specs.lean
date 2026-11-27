import Aegis.MinLength.Code.Funs

/-!
# Specifications of `Aegis.MinLength.min_length`

LeetCode problem `smallest-substring-with-identical-characters-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinLength

def bytesOf (s : Slice U8) : List ℕ := s.val.map (fun b => b.val)

def byteAt (t : List ℕ) (i : ℕ) : ℕ := t.getD i 0

def IsBinBytes (t : List ℕ) : Prop := ∀ i, i < t.length → byteAt t i = 48 ∨ byteAt t i = 49

def mismatches (s t : List ℕ) : ℕ :=
  ((List.range s.length).filter (fun i => byteAt s i ≠ byteAt t i)).length

def runFinset (t : List ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range t.length).product (Finset.range t.length)).filter
    (fun p => p.1 ≤ p.2 ∧ ∀ i ∈ Finset.Icc p.1 p.2, byteAt t i = byteAt t p.1)

def longestRun (t : List ℕ) : ℕ := (runFinset t).sup (fun p => p.2 - p.1 + 1)

def altBytes (n b : ℕ) : List ℕ :=
  (List.range n).map (fun i => if i % 2 = 0 then 48 + b else 49 - b)

def compByte (b : U8) : U8 := if b.val = 48 then (49#u8) else (48#u8)

def compSlice (s : Slice U8) : Slice U8 :=
  { leng := (s.val.map compByte).length
    list := Aeneas.Data.ListN.ListN.fromList (s.val.map compByte)
    bound := by
      simp only [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length, List.length_map] at *
      exact s.bound }

def revSlice (s : Slice U8) : Slice U8 :=
  { leng := s.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
    bound := by
      simp only [List.length_reverse, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length] at *
      exact s.bound }

/-- Let n = len(s). For a byte array t of length n with t[i] in {48,49} for every 0 <= i < n, let R(t) be the maximum of b-a+1 over all integers a,b with 0 <= a <= b < n and t[i] = t[a] for every i with a <= i <= b. Let H(s,t) be the number of indices i with 0 <= i < n and s[i] != t[i]. The function returns a result r, i.e. min_length(s, numOps) = Result.ok r, such that r = min { R(t) | len(t)=n, t[i] in {48,49} for every i with 0 <= i < n, and H(s,t) <= numOps }.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_1 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      (∀ t : List ℕ, t.length = (bytesOf s).length → IsBinBytes t →
        mismatches (bytesOf s) t ≤ numOps.val → r.val ≤ (longestRun t : ℤ)) ∧
      (∃ t : List ℕ, t.length = (bytesOf s).length ∧ IsBinBytes t ∧
        mismatches (bytesOf s) t ≤ numOps.val ∧ (longestRun t : ℤ) = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      (∀ t : List ℕ, t.length = (bytesOf s).length → IsBinBytes t →
        mismatches (bytesOf s) t ≤ numOps.val → r.val ≤ (longestRun t : ℤ)) ∧
      (∃ t : List ℕ, t.length = (bytesOf s).length ∧ IsBinBytes t ∧
        mismatches (bytesOf s) t ≤ numOps.val ∧ (longestRun t : ℤ) = r.val)) := by
  sorry

/-- The function does not fail: there exists an integer r such that min_length(s, numOps) = Result.ok r.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_2 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r) := by
  sorry

/-- The function returns a result r and 1 <= r <= n.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_3 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      1 ≤ r.val ∧ r.val ≤ ((bytesOf s).length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      1 ≤ r.val ∧ r.val ≤ ((bytesOf s).length : ℤ)) := by
  sorry

/-- The function returns a result r and r equals the maximum of b-a+1 over all integers a,b with 0 <= a <= b < n and s[i] = s[a] for every i with a <= i <= b.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); numOps = 0 and 0 <= numOps <= n. -/
theorem spec_4 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hzero : numOps.val = 0) (hlo : 0 ≤ numOps.val)
    (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      r.val = (longestRun (bytesOf s) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hzero : numOps.val = 0) (hlo : 0 ≤ numOps.val)
    (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      r.val = (longestRun (bytesOf s) : ℤ)) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); numOps = n and 0 <= numOps <= n. -/
theorem spec_5 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hn : numOps.val = ((bytesOf s).length : ℤ))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧ r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hn : numOps.val = ((bytesOf s).length : ℤ))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧ r.val = 1) := by
  sorry

/-- Let n = len(s). For b in {0,1}, define alt_b as the byte array of length n by alt_b[i] = 48+b if i is even, and alt_b[i] = 49-b if i is odd. Let H(s,alt_b) be the number of indices i with 0 <= i < n and s[i] != alt_b[i]. The returned value r satisfies r = 1 if and only if H(s,alt_0) <= numOps or H(s,alt_1) <= numOps.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_6 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      (r.val = 1 ↔
        mismatches (bytesOf s) (altBytes (bytesOf s).length 0) ≤ numOps.val ∨
        mismatches (bytesOf s) (altBytes (bytesOf s).length 1) ≤ numOps.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      (r.val = 1 ↔
        mismatches (bytesOf s) (altBytes (bytesOf s).length 0) ≤ numOps.val ∨
        mismatches (bytesOf s) (altBytes (bytesOf s).length 1) ≤ numOps.val)) := by
  sorry

/-- Let n = len(s). The returned value r equals n if and only if n = 1 or (numOps = 0 and for every i with 0 <= i < n, s[i] = s[0]).
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_7 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      (r.val = ((bytesOf s).length : ℤ) ↔
        (bytesOf s).length = 1 ∨
          (numOps.val = 0 ∧ ∀ i, i < (bytesOf s).length →
            byteAt (bytesOf s) i = byteAt (bytesOf s) 0)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      (r.val = ((bytesOf s).length : ℤ) ↔
        (bytesOf s).length = 1 ∨
          (numOps.val = 0 ∧ ∀ i, i < (bytesOf s).length →
            byteAt (bytesOf s) i = byteAt (bytesOf s) 0))) := by
  sorry

/-- The function returns a result r and there exists a byte array t of length n such that t[i] in {48,49} for every 0 <= i < n, the number of indices i with s[i] != t[i] is at most numOps, and R(t) = r, where R(t) is the maximum of b-a+1 over all 0 <= a <= b < n with t[i] = t[a] for every a <= i <= b.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_8 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      ∃ t : List ℕ, t.length = (bytesOf s).length ∧ IsBinBytes t ∧
        mismatches (bytesOf s) t ≤ numOps.val ∧ (longestRun t : ℤ) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      ∃ t : List ℕ, t.length = (bytesOf s).length ∧ IsBinBytes t ∧
        mismatches (bytesOf s) t ≤ numOps.val ∧ (longestRun t : ℤ) = r.val) := by
  sorry

/-- The function returns a result r and for every byte array t of length n with t[i] in {48,49} for every 0 <= i < n and with at most numOps indices i where s[i] != t[i], we have R(t) >= r, where R(t) is the maximum of b-a+1 over all 0 <= a <= b < n with t[i] = t[a] for every a <= i <= b.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_9 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      ∀ t : List ℕ, t.length = (bytesOf s).length → IsBinBytes t →
        mismatches (bytesOf s) t ≤ numOps.val → r.val ≤ (longestRun t : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      ∀ t : List ℕ, t.length = (bytesOf s).length → IsBinBytes t →
        mismatches (bytesOf s) t ≤ numOps.val → r.val ≤ (longestRun t : ℤ)) := by
  sorry

/-- The function returns a result r and r <= R(s), where R(s) is the maximum of b-a+1 over all 0 <= a <= b < n with s[i] = s[a] for every a <= i <= b.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_10 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      r.val ≤ (longestRun (bytesOf s) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r ∧
      r.val ≤ (longestRun (bytesOf s) : ℤ)) := by
  sorry

/-- Let r be the result for budget numOps. For every integer k with numOps <= k <= n, if r_k is the result of min_length(s, k), then r_k <= r. In words, increasing the allowed number of flips cannot increase the minimum achievable longest equal-character run.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_11 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∀ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r →
      ∀ k : I64, numOps.val ≤ k.val → k.val ≤ ((bytesOf s).length : ℤ) →
        ∀ rk : I64, Aegis.MinLength.min_length s k = Result.ok rk → rk.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∀ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r →
      ∀ k : I64, numOps.val ≤ k.val → k.val ≤ ((bytesOf s).length : ℤ) →
        ∀ rk : I64, Aegis.MinLength.min_length s k = Result.ok rk → rk.val ≤ r.val) := by
  sorry

/-- Let comp(s) be the byte array of length n with comp(s)[i] = 49 if s[i] = 48, and comp(s)[i] = 48 if s[i] = 49. If the function returns r for s, then min_length(comp(s), numOps) also returns r.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_12 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∀ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r →
      Aegis.MinLength.min_length (compSlice s) numOps = Result.ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∀ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r →
      Aegis.MinLength.min_length (compSlice s) numOps = Result.ok r) := by
  sorry

/-- Let rev(s) be the byte array of length n with rev(s)[i] = s[n-1-i]. If the function returns r for s, then min_length(rev(s), numOps) also returns r.
  Preconditions: Let n = len(s). 1 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 48 (character '0') or 49 (character '1'); 0 <= numOps <= n. -/
theorem spec_13 (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)) :
    ∀ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r →
      Aegis.MinLength.min_length (revSlice s) numOps = Result.ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (numOps : I64)
    (hn_pos : 1 ≤ (bytesOf s).length) (hn_le : (bytesOf s).length ≤ 1000)
    (hbin : IsBinBytes (bytesOf s))
    (hlo : 0 ≤ numOps.val) (hhi : numOps.val ≤ ((bytesOf s).length : ℤ)), ∀ r : I64, Aegis.MinLength.min_length s numOps = Result.ok r →
      Aegis.MinLength.min_length (revSlice s) numOps = Result.ok r) := by
  sorry

end AegisSpec.MinLength
