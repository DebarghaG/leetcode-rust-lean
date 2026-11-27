import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `apply-operations-to-make-two-strings-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def isBitByte (b : Std.U8) : Prop := b.val = 48 ∨ b.val = 49

def AllBits (s : Slice Std.U8) : Prop := ∀ i b, s.get? i = some b → isBitByte b

def mismatchSet (s1 s2 : Slice Std.U8) : Finset ℕ :=
  (Finset.range s1.length).filter fun i => s1.get? i ≠ s2.get? i

def mismatchCount (s1 s2 : Slice Std.U8) : ℕ := (mismatchSet s1 s2).card

def IsPerfectMatching (M : Finset ℕ) (P : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ P, p.1 < p.2 ∧ p.1 ∈ M ∧ p.2 ∈ M) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
    (∀ i ∈ M, ∃ p ∈ P, p.1 = i ∨ p.2 = i)

def matchingCost (x : ℤ) (P : Finset (ℕ × ℕ)) : ℤ :=
  Finset.sum P fun p => min x ((p.2 : ℤ) - (p.1 : ℤ))

noncomputable def perfectMatchings (M : Finset ℕ) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact (M.product M).powerset.filter (fun P => IsPerfectMatching M P)

noncomputable def minMatchingCost (M : Finset ℕ) (x : ℤ) : ℤ :=
  if h : (perfectMatchings M).Nonempty then
    ((perfectMatchings M).image (matchingCost x)).min' (h.image (matchingCost x))
  else 0

noncomputable def increasingElems (M : Finset ℕ) : List ℕ := M.toList.insertionSort (· ≤ ·)

def consecutivePairSum : List ℕ → ℤ
  | a :: b :: rest => ((b : ℤ) - (a : ℤ)) + consecutivePairSum rest
  | _ => 0

def consecutivePairMinSum (x : ℤ) : List ℕ → ℤ
  | a :: b :: rest => min x ((b : ℤ) - (a : ℤ)) + consecutivePairMinSum x rest
  | _ => 0

inductive Op where

  | flipTwo (i j : ℕ)

  | flipAdj (i : ℕ)

def Op.cost (x : ℤ) : Op → ℤ
  | .flipTwo _ _ => x
  | .flipAdj _ => 1

def Op.Allowed (n : ℕ) : Op → Prop
  | .flipTwo i j => i < n ∧ j < n ∧ i ≠ j
  | .flipAdj i => i + 1 < n

def flipVal (v : ℕ) : ℕ := if v = 48 then 49 else if v = 49 then 48 else v

def flipPos (l : List ℕ) (i : ℕ) : List ℕ := l.set i (flipVal (l.getD i 0))

def Op.apply : Op → List ℕ → List ℕ
  | .flipTwo i j, l => flipPos (flipPos l i) j
  | .flipAdj i, l => flipPos (flipPos l i) (i + 1)

def runOps (ops : List Op) (l : List ℕ) : List ℕ := ops.foldl (fun l op => op.apply l) l

def opsCost (x : ℤ) (ops : List Op) : ℤ := (ops.map (Op.cost x)).sum

def byteVals (s : Slice Std.U8) : List ℕ := s.val.map fun b => b.val

def Transforms (s1 s2 : Slice Std.U8) (ops : List Op) : Prop :=
  (∀ op ∈ ops, op.Allowed s1.length) ∧ runOps ops (byteVals s1) = byteVals s2

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. Whenever min_operations(s1, s2, x) returns a result r, the following holds: if k is odd then r = -1; if k is even then r is the minimum, over all perfect matchings P of M, of the sum over unordered pairs {i,j} in P of min(x, |i-j|). A perfect matching of M is a partition of M into unordered pairs; the empty set has the unique empty perfect matching, whose sum is 0. Here |i-j| is the absolute difference of the indices.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_1 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      (Odd (mismatchCount s1 s2) → r.val = -1) ∧
        (Even (mismatchCount s1 s2) →
          r.val = minMatchingCost (mismatchSet s1 s2) x.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      (Odd (mismatchCount s1 s2) → r.val = -1) ∧
        (Even (mismatchCount s1 s2) →
          r.val = minMatchingCost (mismatchSet s1 s2) x.val)) := by
  sorry

/-- For every input satisfying the preconditions, the call min_operations(s1, s2, x) returns a result r; it does not fail (in particular, it does not overflow, access out of bounds, or panic).
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_2 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∃ r, Aegis.MinOperations.min_operations s1 s2 x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∃ r, Aegis.MinOperations.min_operations s1 s2 x = ok r) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. If k is odd, then whenever min_operations(s1, s2, x) returns a result r, r = -1.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_3 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Odd (mismatchCount s1 s2)) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val = -1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Odd (mismatchCount s1 s2)), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val = -1) := by
  sorry

/-- If s1[i] = s2[i] for every i with 0 <= i < n, then whenever min_operations(s1, s2, x) returns a result r, r = 0.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_4 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (heq : ∀ i, i < s1.length → s1.get? i = s2.get? i) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (heq : ∀ i, i < s1.length → s1.get? i = s2.get? i), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val = 0) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] }. If M = {i, j} with 0 <= i < j < n, then whenever min_operations(s1, s2, x) returns a result r, r = min(x, j - i).
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_5 (s1 s2 : Slice Std.U8) (x : Std.I64) (i j : ℕ)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hij : i < j) (hj : j < s1.length)
    (hM : mismatchSet s1 s2 = {i, j}) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val = min x.val ((j : ℤ) - (i : ℤ)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64) (i j : ℕ)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hij : i < j) (hj : j < s1.length)
    (hM : mismatchSet s1 s2 = {i, j}), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val = min x.val ((j : ℤ) - (i : ℤ))) := by
  sorry

/-- Let n = len(s1). If n is even and s1[i] != s2[i] for every i with 0 <= i < n, then whenever min_operations(s1, s2, x) returns a result r, r = n/2.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_6 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hn : Even s1.length)
    (hdiff : ∀ i, i < s1.length → s1.get? i ≠ s2.get? i) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val = ((s1.length / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hn : Even s1.length)
    (hdiff : ∀ i, i < s1.length → s1.get? i ≠ s2.get? i), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val = ((s1.length / 2 : ℕ) : ℤ)) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. If x = 1, then whenever min_operations(s1, s2, x) returns a result r, r = k/2 if k is even and r = -1 if k is odd.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_7 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hx : x.val = 1) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      (Even (mismatchCount s1 s2) → r.val = ((mismatchCount s1 s2 / 2 : ℕ) : ℤ)) ∧
        (Odd (mismatchCount s1 s2) → r.val = -1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hx : x.val = 1), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      (Even (mismatchCount s1 s2) → r.val = ((mismatchCount s1 s2 / 2 : ℕ) : ℤ)) ∧
        (Odd (mismatchCount s1 s2) → r.val = -1)) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. If k is even, then whenever min_operations(s1, s2, x) returns a result r, k/2 <= r <= (k/2) * x.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_8 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Even (mismatchCount s1 s2)) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      ((mismatchCount s1 s2 / 2 : ℕ) : ℤ) ≤ r.val ∧
        r.val ≤ ((mismatchCount s1 s2 / 2 : ℕ) : ℤ) * x.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Even (mismatchCount s1 s2)), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      ((mismatchCount s1 s2 / 2 : ℕ) : ℤ) ≤ r.val ∧
        r.val ≤ ((mismatchCount s1 s2 / 2 : ℕ) : ℤ) * x.val) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. If k is even and the elements of M in increasing order are a_0 < a_1 < ... < a_{k-1} (with k=0 giving the empty sum 0), then whenever min_operations(s1, s2, x) returns a result r, r <= sum_{t=0,2,4,...,k-2} (a_{t+1} - a_t).
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_9 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Even (mismatchCount s1 s2)) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val ≤ consecutivePairSum (increasingElems (mismatchSet s1 s2)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Even (mismatchCount s1 s2)), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val ≤ consecutivePairSum (increasingElems (mismatchSet s1 s2))) := by
  sorry

/-- Whenever min_operations(s1, s2, x1) returns a result r1 and min_operations(s1, s2, x2) returns a result r2, r1 <= r2.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500; 1 <= x1 <= x2 <= 500; and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_10 (s1 s2 : Slice Std.U8) (x1 x2 : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2 : x2.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∀ r1 r2, Aegis.MinOperations.min_operations s1 s2 x1 = ok r1 →
      Aegis.MinOperations.min_operations s1 s2 x2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x1 x2 : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2 : x2.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∀ r1 r2, Aegis.MinOperations.min_operations s1 s2 x1 = ok r1 →
      Aegis.MinOperations.min_operations s1 s2 x2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever min_operations(s1, s2, x) returns a result r and min_operations(t1, t2, x) returns a result r', r = r'.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2) = len(t1) = len(t2), 1 <= n <= 500, 1 <= x <= 500, every byte of s1, s2, t1, t2 is an ASCII code of '0' or '1' (48 or 49), and for every i with 0 <= i < n, s1[i] != s2[i] if and only if t1[i] != t2[i]. -/
theorem spec_11 (s1 s2 t1 t2 : Slice Std.U8) (x : Std.I64)
    (hlen1 : s1.length = s2.length)
    (hlen2 : s1.length = t1.length)
    (hlen3 : s1.length = t2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hbits3 : AllBits t1) (hbits4 : AllBits t2)
    (hmis : ∀ i, i < s1.length → (s1.get? i ≠ s2.get? i ↔ t1.get? i ≠ t2.get? i)) :
    ∀ r r', Aegis.MinOperations.min_operations s1 s2 x = ok r →
      Aegis.MinOperations.min_operations t1 t2 x = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s1 s2 t1 t2 : Slice Std.U8) (x : Std.I64)
    (hlen1 : s1.length = s2.length)
    (hlen2 : s1.length = t1.length)
    (hlen3 : s1.length = t2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hbits3 : AllBits t1) (hbits4 : AllBits t2)
    (hmis : ∀ i, i < s1.length → (s1.get? i ≠ s2.get? i ↔ t1.get? i ≠ t2.get? i)), ∀ r r', Aegis.MinOperations.min_operations s1 s2 x = ok r →
      Aegis.MinOperations.min_operations t1 t2 x = ok r' → r = r') := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] }. Whenever min_operations(s1, s2, x) returns a result r and r != -1, there exists a finite sequence of allowed operations whose total cost is exactly r and which transforms s1 into s2. Allowed operations are: flip any two positions i and j of s1 at cost x, and flip positions i and i+1 of s1 at cost 1 for 0 <= i < n-1.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_12 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val ≠ -1 →
      ∃ ops : List Op, Transforms s1 s2 ops ∧ opsCost x.val ops = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val ≠ -1 →
      ∃ ops : List Op, Transforms s1 s2 ops ∧ opsCost x.val ops = r.val) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] }. Whenever min_operations(s1, s2, x) returns a result r and r != -1, every finite sequence of allowed operations that transforms s1 into s2 has total cost at least r.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_13 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val ≠ -1 →
      ∀ ops : List Op, Transforms s1 s2 ops → r.val ≤ opsCost x.val ops := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r → r.val ≠ -1 →
      ∀ ops : List Op, Transforms s1 s2 ops → r.val ≤ opsCost x.val ops) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] }. Assume x >= n - 1. If k = |M| is even and the elements of M in increasing order are a_0 < a_1 < ... < a_{k-1} (for k=0 the sum below is 0), then whenever min_operations(s1, s2, x) returns a result r, r = sum_{t=0,2,4,...,k-2} (a_{t+1} - a_t).
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, x >= n - 1, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_14 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hxn : ((s1.length : ℤ) - 1) ≤ x.val)
    (hk : Even (mismatchCount s1 s2)) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val = consecutivePairSum (increasingElems (mismatchSet s1 s2)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hxn : ((s1.length : ℤ) - 1) ≤ x.val)
    (hk : Even (mismatchCount s1 s2)), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val = consecutivePairSum (increasingElems (mismatchSet s1 s2))) := by
  sorry

/-- Whenever min_operations(s1, s2, x) returns a result r and min_operations(s2, s1, x) returns a result r', r = r'.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_15 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∀ r r', Aegis.MinOperations.min_operations s1 s2 x = ok r →
      Aegis.MinOperations.min_operations s2 s1 x = ok r' → r = r' := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∀ r r', Aegis.MinOperations.min_operations s1 s2 x = ok r →
      Aegis.MinOperations.min_operations s2 s1 x = ok r' → r = r') := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. If k is even and the elements of M in increasing order are a_0 < a_1 < ... < a_{k-1} (with k=0 giving the empty sum 0), then whenever min_operations(s1, s2, x) returns a result r, r <= sum_{t=0,2,4,...,k-2} min(x, a_{t+1} - a_t).
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_16 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Even (mismatchCount s1 s2)) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val ≤ consecutivePairMinSum x.val (increasingElems (mismatchSet s1 s2)) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2)
    (hk : Even (mismatchCount s1 s2)), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      r.val ≤ consecutivePairMinSum x.val (increasingElems (mismatchSet s1 s2))) := by
  sorry

/-- Let M = { i | 0 <= i < n and s1[i] != s2[i] } and k = |M|. Whenever min_operations(s1, s2, x) returns a result r, r = -1 if and only if k is odd.
  Preconditions: Let n = len(s1). Assume len(s1) = len(s2), 1 <= n <= 500, 1 <= x <= 500, and for every i with 0 <= i < n, s1[i] and s2[i] are ASCII codes of '0' or '1' (48 or 49). -/
theorem spec_17 (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2) :
    ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      (r.val = -1 ↔ Odd (mismatchCount s1 s2)) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (x : Std.I64)
    (hlen : s1.length = s2.length)
    (hn1 : 1 ≤ s1.length) (hn2 : s1.length ≤ 500)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 500)
    (hbits1 : AllBits s1) (hbits2 : AllBits s2), ∀ r, Aegis.MinOperations.min_operations s1 s2 x = ok r →
      (r.val = -1 ↔ Odd (mismatchCount s1 s2))) := by
  sorry

end AegisSpec.MinOperations
