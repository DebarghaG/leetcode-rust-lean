import Aegis.FindPermutation.Code.Funs

/-!
# Specifications of `Aegis.FindPermutation.find_permutation`

LeetCode problem `find-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindPermutation

abbrev ByteSlice := Aeneas.Std.Slice Aeneas.Std.U8

abbrev I64Vec := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

def iota (n : ℕ) : List ℤ := (List.range n).map (fun k => (k : ℤ) + 1)

def PermOfRange (l : List ℤ) (n : ℕ) : Prop := l.Perm (iota n)

def intVals (r : I64Vec) : List ℤ := r.val.map (fun x => x.val)

def ValidInput (s : ByteSlice) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100000 ∧
    (∀ b ∈ s.val, b.val = 73 ∨ b.val = 68)

def Compatible (s : ByteSlice) (r : List ℤ) : Prop :=
  ∀ i : ℕ, i < s.val.length →
    ((s.val[i]!.val = 73 → r[i]! < r[i+1]!) ∧
     (s.val[i]!.val = 68 → r[i]! > r[i+1]!))

def FirstDiffLt (r q : List ℤ) : Prop :=
  ∀ k : ℕ, (∀ j : ℕ, j < k → q[j]? = r[j]?) → q[k]? ≠ r[k]? → r[k]! < q[k]!

def leadingDCount (s : ByteSlice) : ℕ :=
  (s.val.takeWhile (fun b => b.val == 68)).length

def trailingDCount (s : ByteSlice) : ℕ :=
  (s.val.reverse.takeWhile (fun b => b.val == 68)).length

/-- Whenever the function returns a result r, let n = len(s)+1. Then r is exactly the lexicographically smallest permutation of {1,2,...,n} compatible with s: (a) len(r) = n; (b) the entries of r are exactly the integers 1,2,...,n, each appearing once; (c) for every i with 0 <= i < len(s), if s[i] = 73 ('I') then r[i] < r[i+1], and if s[i] = 68 ('D') then r[i] > r[i+1]; (d) for every vector q of length n whose entries are exactly 1,2,...,n and which satisfies (c) with q in place of r, either q = r, or at the smallest index k with q[k] != r[k] we have r[k] < q[k].
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_1
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r) :
    r.val.length = s.val.length + 1 ∧
    PermOfRange (intVals r) (s.val.length + 1) ∧
    Compatible s (intVals r) ∧
    (∀ q : List ℤ,
      q.length = s.val.length + 1 →
      PermOfRange q (s.val.length + 1) →
      Compatible s q →
      q = intVals r ∨ FirstDiffLt (intVals r) q) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r), r.val.length = s.val.length + 1 ∧
    PermOfRange (intVals r) (s.val.length + 1) ∧
    Compatible s (intVals r) ∧
    (∀ q : List ℤ,
      q.length = s.val.length + 1 →
      PermOfRange q (s.val.length + 1) →
      Compatible s q →
      q = intVals r ∨ FirstDiffLt (intVals r) q)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access out of bounds.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_2
    (s : ByteSlice) (hs : ValidInput s) :
    ∃ r : I64Vec, Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s), ∃ r : I64Vec, Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(s) + 1.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_3
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r) :
    r.val.length = s.val.length + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r), r.val.length = s.val.length + 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= len(s) + 1.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_4
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r) :
    ∀ i : ℕ, i < r.val.length → 1 ≤ r.val[i]!.val ∧ r.val[i]!.val ≤ (s.val.length : ℤ) + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r), ∀ i : ℕ, i < r.val.length → 1 ≤ r.val[i]!.val ∧ r.val[i]!.val ≤ (s.val.length : ℤ) + 1) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_5
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r) :
    ∀ i j : ℕ, i < j → j < r.val.length → r.val[i]! ≠ r.val[j]! := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r), ∀ i j : ℕ, i < j → j < r.val.length → r.val[i]! ≠ r.val[j]!) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(s) + 1, for every i with 0 <= i < len(s), if s[i] = 73 ('I') then r[i] < r[i+1], and if s[i] = 68 ('D') then r[i] > r[i+1].
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_6
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1) :
    Compatible s (intVals r) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1), Compatible s (intVals r)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(s) + 1, let n = len(s)+1. For every vector q such that len(q) = n, q is a permutation of 1,2,...,n, and q satisfies the same I/D comparisons as r for s, if q != r then, letting k be the smallest index with q[k] != r[k], we have r[k] < q[k].
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_7
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1) :
    ∀ q : List ℤ,
      q.length = s.val.length + 1 →
      PermOfRange q (s.val.length + 1) →
      Compatible s q →
      q ≠ intVals r →
      FirstDiffLt (intVals r) q := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1), ∀ q : List ℤ,
      q.length = s.val.length + 1 →
      PermOfRange q (s.val.length + 1) →
      Compatible s q →
      q ≠ intVals r →
      FirstDiffLt (intVals r) q) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(s) + 1, let n = len(s)+1. For every i with 0 <= i < n and every vector q that is a permutation of 1,2,...,n satisfying the I/D comparisons for s, if q[j] = r[j] for all j with 0 <= j < i, then r[i] <= q[i].
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_8
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1) :
    ∀ i : ℕ, i < s.val.length + 1 →
      ∀ q : List ℤ,
        q.length = s.val.length + 1 →
        PermOfRange q (s.val.length + 1) →
        Compatible s q →
        (∀ j : ℕ, j < i → q[j]? = (intVals r)[j]?) →
        (intVals r)[i]! ≤ q[i]! := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1), ∀ i : ℕ, i < s.val.length + 1 →
      ∀ q : List ℤ,
        q.length = s.val.length + 1 →
        PermOfRange q (s.val.length + 1) →
        Compatible s q →
        (∀ j : ℕ, j < i → q[j]? = (intVals r)[j]?) →
        (intVals r)[i]! ≤ q[i]!) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(s) + 1, let k be the largest integer with 0 <= k <= len(s) such that for every j with 0 <= j < k, s[j] = 68 ('D'). Then r[0] = k + 1.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_9
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1) :
    r.val[0]!.val = (leadingDCount s : ℤ) + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1), r.val[0]!.val = (leadingDCount s : ℤ) + 1) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(s) + 1, let n = len(s)+1 and let k be the largest integer with 0 <= k <= len(s) such that for every j with len(s)-k <= j < len(s), s[j] = 68 ('D'). Then r[n-1] = n - k.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_10
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1) :
    r.val[s.val.length]!.val = ((s.val.length : ℤ) + 1) - (trailingDCount s : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1), r.val[s.val.length]!.val = ((s.val.length : ℤ) + 1) - (trailingDCount s : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(s) + 1, for every pair of indices a,b with 0 <= a <= b < len(s) such that s[j] = 68 ('D') for every j with a <= j <= b, and either a = 0 or s[a-1] = 73 ('I'), and either b = len(s)-1 or s[b+1] = 73 ('I'), we have for every t with 0 <= t <= b-a+1: r[a+t] = b+2-t.
  Preconditions: len(s) >= 1; len(s) <= 100000; for every i with 0 <= i < len(s), s[i] = 73 ('I') or s[i] = 68 ('D'). -/
theorem spec_11
    (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1) :
    ∀ a b : ℕ, a ≤ b → b < s.val.length →
      (∀ j : ℕ, a ≤ j → j ≤ b → s.val[j]!.val = 68) →
      (a = 0 ∨ s.val[a - 1]!.val = 73) →
      (b = s.val.length - 1 ∨ s.val[b + 1]!.val = 73) →
      ∀ t : ℕ, t ≤ b - a + 1 → r.val[a + t]!.val = (b : ℤ) + 2 - (t : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : ByteSlice) (hs : ValidInput s)
    (r : I64Vec) (h : Aegis.FindPermutation.find_permutation s = Aeneas.Std.Result.ok r)
    (hlen : r.val.length = s.val.length + 1), ∀ a b : ℕ, a ≤ b → b < s.val.length →
      (∀ j : ℕ, a ≤ j → j ≤ b → s.val[j]!.val = 68) →
      (a = 0 ∨ s.val[a - 1]!.val = 73) →
      (b = s.val.length - 1 ∨ s.val[b + 1]!.val = 73) →
      ∀ t : ℕ, t ≤ b - a + 1 → r.val[a + t]!.val = (b : ℤ) + 2 - (t : ℤ)) := by
  sorry

end AegisSpec.FindPermutation
