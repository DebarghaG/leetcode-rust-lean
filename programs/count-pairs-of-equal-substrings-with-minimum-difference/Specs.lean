import Aegis.CountQuadruples.Code.Funs

/-!
# Specifications of `Aegis.CountQuadruples.count_quadruples`

LeetCode problem `count-pairs-of-equal-substrings-with-minimum-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountQuadruples

set_option maxHeartbeats 1000000

namespace AegisSpec.CountQuadruples

def IsLower (c : ℕ) : Prop := 97 ≤ c ∧ c ≤ 122

def AllLower (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, IsLower b.val

def bvals (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

@[simp]
theorem bvals_length (s : Slice Std.U8) : (bvals s).length = s.val.length := by
  simp [bvals]

structure Quad where
  i : ℕ
  j : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr

def substr (xs : List ℕ) (i j : ℕ) : List ℕ := (xs.drop i).take (j + 1 - i)

def quadRange (m n : ℕ) : Finset Quad :=
  (((Finset.range m).product (Finset.range m)).product
      ((Finset.range n).product (Finset.range n))).image
    (fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩)

def IsMatch (xs ys : List ℕ) (q : Quad) : Prop :=
  q.i ≤ q.j ∧ q.j < xs.length ∧ q.a ≤ q.b ∧ q.b < ys.length ∧
    substr xs q.i q.j = substr ys q.a q.b

instance decidablePredIsMatch (xs ys : List ℕ) : DecidablePred (IsMatch xs ys) := fun q => by
  unfold IsMatch
  infer_instance

def Q (xs ys : List ℕ) : Finset Quad := (quadRange xs.length ys.length).filter (IsMatch xs ys)

def diffs (xs ys : List ℕ) : Finset ℤ := (Q xs ys).image (fun q => (q.j : ℤ) - (q.a : ℤ))

noncomputable def Dmin (xs ys : List ℕ) (hQ : (Q xs ys).Nonempty) : ℤ :=
  (diffs xs ys).min' (hQ.image (fun q => (q.j : ℤ) - (q.a : ℤ)))

def atDiff (xs ys : List ℕ) (D : ℤ) : Finset Quad :=
  (Q xs ys).filter (fun q => (q.j : ℤ) - (q.a : ℤ) = D)

def IsMinDiff (xs ys : List ℕ) (q : Quad) : Prop :=
  q ∈ Q xs ys ∧ ∀ q' ∈ Q xs ys, (q.j : ℤ) - (q.a : ℤ) ≤ (q'.j : ℤ) - (q'.a : ℤ)

def blockLen (q : Quad) : ℤ := (q.j : ℤ) - (q.i : ℤ) + 1

def commonBytes (xs ys : List ℕ) : Finset ℕ :=
  (Finset.Icc 97 122).filter (fun c => c ∈ xs ∧ c ∈ ys)

def firstIdx (xs : List ℕ) (c : ℕ) : ℕ := xs.idxOf c

def lastIdx (xs : List ℕ) (c : ℕ) : ℕ := xs.length - 1 - xs.reverse.idxOf c

def cdiff (xs ys : List ℕ) (c : ℕ) : ℤ := (firstIdx xs c : ℤ) - (lastIdx ys c : ℤ)

def cdiffs (xs ys : List ℕ) : Finset ℤ := (commonBytes xs ys).image (cdiff xs ys)

noncomputable def Dc (xs ys : List ℕ) (hC : (commonBytes xs ys).Nonempty) : ℤ :=
  (cdiffs xs ys).min' (hC.image (cdiff xs ys))

def charPairs (xs ys : List ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range xs.length).product (Finset.range ys.length)).filter
    (fun p => xs[p.1]? = ys[p.2]?)

def charDiffs (xs ys : List ℕ) : Finset ℤ :=
  (charPairs xs ys).image (fun p => (p.1 : ℤ) - (p.2 : ℤ))

noncomputable def Dchar (xs ys : List ℕ) (h : (charPairs xs ys).Nonempty) : ℤ :=
  (charDiffs xs ys).min' (h.image (fun p => (p.1 : ℤ) - (p.2 : ℤ)))

def pairCount (xs ys : List ℕ) (c : ℕ) (D : ℤ) : ℕ :=
  (((Finset.range xs.length).product (Finset.range ys.length)).filter
      (fun p => xs[p.1]? = some c ∧ ys[p.2]? = some c ∧ (p.1 : ℤ) - (p.2 : ℤ) = D)).card

/-- Let m = len(first_string) and n = len(second_string). Let Q be the set of all quadruples (i,j,a,b) such that 0 <= i <= j < m, 0 <= a <= b < n, and the inclusive byte substring first_string[i..j] equals second_string[a..b]. The function returns a result r (it does not fail). If Q is empty, then r = 0. If Q is nonempty, let D = min { j - a | (i,j,a,b) in Q }. Then r = |{ (i,j,a,b) in Q | j - a = D }|.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_1 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
      (Q (bvals first_string) (bvals second_string) = ∅ → r.val = 0) ∧
      (∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty),
        r.val = ((atDiff (bvals first_string) (bvals second_string)
          (Dmin (bvals first_string) (bvals second_string) hQ)).card : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
      (Q (bvals first_string) (bvals second_string) = ∅ → r.val = 0) ∧
      (∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty),
        r.val = ((atDiff (bvals first_string) (bvals second_string)
          (Dmin (bvals first_string) (bvals second_string) hQ)).card : ℤ))) := by
  sorry

/-- For every first_string and second_string satisfying the preconditions, the function returns some result r; it does not fail, overflow, go out of bounds, or panic.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_2 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∃ r : Std.I64, count_quadruples first_string second_string = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∃ r : Std.I64, count_quadruples first_string second_string = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_3 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= |C|, where C = { c in {97,98,...,122} | c occurs at least once in first_string and at least once in second_string }. In particular, r <= 26.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_4 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r →
      r.val ≤ ((commonBytes (bvals first_string) (bvals second_string)).card : ℤ) ∧
      r.val ≤ 26 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r →
      r.val ≤ ((commonBytes (bvals first_string) (bvals second_string)).card : ℤ) ∧
      r.val ≤ 26) := by
  sorry

/-- The function returns r and r = 0 if and only if no byte value occurs in both first_string and second_string; equivalently, there are no indices p,q with 0 <= p < len(first_string), 0 <= q < len(second_string), and first_string[p] = second_string[q].
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_5 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
      (r.val = 0 ↔
        ¬ ∃ (p : Fin (bvals first_string).length) (q : Fin (bvals second_string).length),
          (bvals first_string).get p = (bvals second_string).get q) ∧
      (r.val = 0 ↔ ∀ c : ℕ, c ∈ bvals first_string → c ∈ bvals second_string → False) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
      (r.val = 0 ↔
        ¬ ∃ (p : Fin (bvals first_string).length) (q : Fin (bvals second_string).length),
          (bvals first_string).get p = (bvals second_string).get q) ∧
      (r.val = 0 ↔ ∀ c : ℕ, c ∈ bvals first_string → c ∈ bvals second_string → False)) := by
  sorry

/-- The function returns r. If r > 0, then the set Q from S1 is nonempty and there exists a quadruple (i,j,a,b) in Q with j - a = min { y - u | (x,y,u,v) in Q }; that is, at least one minimizing quadruple exists and is included in the count.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_6 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
      (0 < r.val →
        (Q (bvals first_string) (bvals second_string)).Nonempty ∧
        ∃ q : Quad, IsMinDiff (bvals first_string) (bvals second_string) q) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
      (0 < r.val →
        (Q (bvals first_string) (bvals second_string)).Nonempty ∧
        ∃ q : Quad, IsMinDiff (bvals first_string) (bvals second_string) q)) := by
  sorry

/-- Whenever the function returns r with r > 0, let Q be the set from spec_1 and D = min { j - a | (i,j,a,b) in Q }. Then -(len(second_string) - 1) <= D <= len(first_string) - 1.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_7 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty),
        -(((bvals second_string).length : ℤ) - 1) ≤
            Dmin (bvals first_string) (bvals second_string) hQ ∧
          Dmin (bvals first_string) (bvals second_string) hQ ≤
            ((bvals first_string).length : ℤ) - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty),
        -(((bvals second_string).length : ℤ) - 1) ≤
            Dmin (bvals first_string) (bvals second_string) hQ ∧
          Dmin (bvals first_string) (bvals second_string) hQ ≤
            ((bvals first_string).length : ℤ) - 1) := by
  sorry

/-- Whenever the function returns r with r > 0, let Q and D be as in spec_1. For every (i,j,a,b) in Q with j - a = D, we have i = j and a = b. Equivalently, every optimal matching substring has length 1.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_8 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty) (q : Quad),
        q ∈ Q (bvals first_string) (bvals second_string) →
        (q.j : ℤ) - (q.a : ℤ) = Dmin (bvals first_string) (bvals second_string) hQ →
        q.i = q.j ∧ q.a = q.b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty) (q : Quad),
        q ∈ Q (bvals first_string) (bvals second_string) →
        (q.j : ℤ) - (q.a : ℤ) = Dmin (bvals first_string) (bvals second_string) hQ →
        q.i = q.j ∧ q.a = q.b) := by
  sorry

/-- Let C be the set of lowercase bytes c (ASCII 97 through 122) that occur in both strings. If C is empty, then the function returns 0. If C is nonempty, for each c in C let f(c) be the least index p with first_string[p] = c, and let l(c) be the greatest index q with second_string[q] = c. Let D = min_{c in C} (f(c) - l(c)). The function returns r and r = |{ c in C | f(c) - l(c) = D }|.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_9 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    (commonBytes (bvals first_string) (bvals second_string) = ∅ →
      ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧ r.val = 0) ∧
    (∀ (hC : (commonBytes (bvals first_string) (bvals second_string)).Nonempty),
      ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
        r.val = (((commonBytes (bvals first_string) (bvals second_string)).filter
          (fun c => cdiff (bvals first_string) (bvals second_string) c =
            Dc (bvals first_string) (bvals second_string) hC)).card : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), (commonBytes (bvals first_string) (bvals second_string) = ∅ →
      ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧ r.val = 0) ∧
    (∀ (hC : (commonBytes (bvals first_string) (bvals second_string)).Nonempty),
      ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
        r.val = (((commonBytes (bvals first_string) (bvals second_string)).filter
          (fun c => cdiff (bvals first_string) (bvals second_string) c =
            Dc (bvals first_string) (bvals second_string) hC)).card : ℤ))) := by
  sorry

/-- Whenever the function returns r with r > 0, let Q and D be as in spec_1. For every (i,j,a,b) in Q with j > i (equivalently, b > a), we have j - a > D.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_10 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty) (q : Quad),
        q ∈ Q (bvals first_string) (bvals second_string) →
        (q.i < q.j → Dmin (bvals first_string) (bvals second_string) hQ <
          (q.j : ℤ) - (q.a : ℤ)) ∧
        (q.a < q.b → Dmin (bvals first_string) (bvals second_string) hQ <
          (q.j : ℤ) - (q.a : ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty) (q : Quad),
        q ∈ Q (bvals first_string) (bvals second_string) →
        (q.i < q.j → Dmin (bvals first_string) (bvals second_string) hQ <
          (q.j : ℤ) - (q.a : ℤ)) ∧
        (q.a < q.b → Dmin (bvals first_string) (bvals second_string) hQ <
          (q.j : ℤ) - (q.a : ℤ))) := by
  sorry

/-- Whenever the function returns r with r > 0, let Q and D be as in spec_1. For every (i,j,a,b) in Q, let L = j - i + 1 (which equals b - a + 1). Then j - a >= D + L - 1.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_11 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty) (q : Quad),
        q ∈ Q (bvals first_string) (bvals second_string) →
        (q.j : ℤ) - (q.a : ℤ) ≥
          Dmin (bvals first_string) (bvals second_string) hQ + blockLen q - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hQ : (Q (bvals first_string) (bvals second_string)).Nonempty) (q : Quad),
        q ∈ Q (bvals first_string) (bvals second_string) →
        (q.j : ℤ) - (q.a : ℤ) ≥
          Dmin (bvals first_string) (bvals second_string) hQ + blockLen q - 1) := by
  sorry

/-- Whenever the function returns r with r > 0, let D = min { p - q | 0 <= p < len(first_string), 0 <= q < len(second_string), first_string[p] = second_string[q] }. For every pair (p,q) with first_string[p] = second_string[q] and p - q = D, p is the first occurrence of first_string[p] in first_string (there is no p' < p with first_string[p'] = first_string[p]) and q is the last occurrence of second_string[q] in second_string (there is no q' > q with second_string[q'] = second_string[q]).
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_12 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hD : (charPairs (bvals first_string) (bvals second_string)).Nonempty)
        (p q : ℕ), p < (bvals first_string).length → q < (bvals second_string).length →
        (bvals first_string)[p]? = (bvals second_string)[q]? →
        (p : ℤ) - (q : ℤ) = Dchar (bvals first_string) (bvals second_string) hD →
        (∀ p' : ℕ, p' < p → (bvals first_string)[p']? ≠ (bvals first_string)[p]?) ∧
        (∀ q' : ℕ, q < q' → q' < (bvals second_string).length →
          (bvals second_string)[q']? ≠ (bvals second_string)[q]?) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ r : Std.I64, count_quadruples first_string second_string = ok r → 0 < r.val →
      ∀ (hD : (charPairs (bvals first_string) (bvals second_string)).Nonempty)
        (p q : ℕ), p < (bvals first_string).length → q < (bvals second_string).length →
        (bvals first_string)[p]? = (bvals second_string)[q]? →
        (p : ℤ) - (q : ℤ) = Dchar (bvals first_string) (bvals second_string) hD →
        (∀ p' : ℕ, p' < p → (bvals first_string)[p']? ≠ (bvals first_string)[p]?) ∧
        (∀ q' : ℕ, q < q' → q' < (bvals second_string).length →
          (bvals second_string)[q']? ≠ (bvals second_string)[q]?)) := by
  sorry

/-- Let C be the set of common lowercase bytes. If C is nonempty, for c in C let f(c) and l(c) be as in spec_9 and let D = min_{c in C}(f(c)-l(c)). Then for every c in C, f(c)-l(c) >= D; moreover the number of pairs (p,q) with first_string[p] = second_string[q] = c and p - q = D is 1 if f(c)-l(c) = D and 0 otherwise. The result r equals the sum over c in C of these numbers.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_13 (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000) :
    ∀ (hC : (commonBytes (bvals first_string) (bvals second_string)).Nonempty),
      ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
        (∀ c : ℕ, c ∈ commonBytes (bvals first_string) (bvals second_string) →
          Dc (bvals first_string) (bvals second_string) hC ≤
            cdiff (bvals first_string) (bvals second_string) c) ∧
        (∀ c : ℕ, c ∈ commonBytes (bvals first_string) (bvals second_string) →
          ((cdiff (bvals first_string) (bvals second_string) c =
              Dc (bvals first_string) (bvals second_string) hC →
            pairCount (bvals first_string) (bvals second_string) c
              (Dc (bvals first_string) (bvals second_string) hC) = 1) ∧
           (cdiff (bvals first_string) (bvals second_string) c ≠
              Dc (bvals first_string) (bvals second_string) hC →
            pairCount (bvals first_string) (bvals second_string) c
              (Dc (bvals first_string) (bvals second_string) hC) = 0))) ∧
        r.val = ((commonBytes (bvals first_string) (bvals second_string)).sum
          (fun c => (pairCount (bvals first_string) (bvals second_string) c
            (Dc (bvals first_string) (bvals second_string) hC) : ℤ))) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (first_string second_string : Slice Std.U8)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000), ∀ (hC : (commonBytes (bvals first_string) (bvals second_string)).Nonempty),
      ∃ r : Std.I64, count_quadruples first_string second_string = ok r ∧
        (∀ c : ℕ, c ∈ commonBytes (bvals first_string) (bvals second_string) →
          Dc (bvals first_string) (bvals second_string) hC ≤
            cdiff (bvals first_string) (bvals second_string) c) ∧
        (∀ c : ℕ, c ∈ commonBytes (bvals first_string) (bvals second_string) →
          ((cdiff (bvals first_string) (bvals second_string) c =
              Dc (bvals first_string) (bvals second_string) hC →
            pairCount (bvals first_string) (bvals second_string) c
              (Dc (bvals first_string) (bvals second_string) hC) = 1) ∧
           (cdiff (bvals first_string) (bvals second_string) c ≠
              Dc (bvals first_string) (bvals second_string) hC →
            pairCount (bvals first_string) (bvals second_string) c
              (Dc (bvals first_string) (bvals second_string) hC) = 0))) ∧
        r.val = ((commonBytes (bvals first_string) (bvals second_string)).sum
          (fun c => (pairCount (bvals first_string) (bvals second_string) c
            (Dc (bvals first_string) (bvals second_string) hC) : ℤ)))) := by
  sorry

/-- Let r be the result on (first_string, second_string). Suppose len(first_string) >= 2 and the last byte of first_string does not occur anywhere in second_string. Let first_string' be first_string with its last byte removed, and let r' be the result on (first_string', second_string). Then the function returns both r and r' and r = r'.
  Preconditions: first_string and second_string are nonempty slices of bytes, each byte is an ASCII lowercase English letter (code 97 through 122), and 1 <= len(first_string), len(second_string) <= 200000. -/
theorem spec_14 (first_string second_string first_string' : Slice Std.U8) (c : ℕ)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000)
    (hlen : 2 ≤ first_string.val.length)
    (hsplit : bvals first_string = bvals first_string' ++ [c])
    (habsent : c ∉ bvals second_string) :
    ∃ r r' : Std.I64, count_quadruples first_string second_string = ok r ∧
      count_quadruples first_string' second_string = ok r' ∧ r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (first_string second_string first_string' : Slice Std.U8) (c : ℕ)
    (hL1 : AllLower first_string) (hL2 : AllLower second_string)
    (h1 : 1 ≤ first_string.val.length) (h2 : first_string.val.length ≤ 200000)
    (h3 : 1 ≤ second_string.val.length) (h4 : second_string.val.length ≤ 200000)
    (hlen : 2 ≤ first_string.val.length)
    (hsplit : bvals first_string = bvals first_string' ++ [c])
    (habsent : c ∉ bvals second_string), ∃ r r' : Std.I64, count_quadruples first_string second_string = ok r ∧
      count_quadruples first_string' second_string = ok r' ∧ r = r') := by
  sorry

end AegisSpec.CountQuadruples
