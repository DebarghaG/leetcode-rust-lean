import Aegis.MinimumSwap.Code.Funs

/-!
# Specifications of `Aegis.MinimumSwap.minimum_swap`

LeetCode problem `minimum-swaps-to-make-strings-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumSwap

namespace AegisSpec.MinimumSwap

abbrev byteX : Std.U8 := 120#u8

abbrev byteY : Std.U8 := 121#u8

def countPairs (p : Std.U8 → Std.U8 → Bool) (s1 s2 : Slice Std.U8) : ℕ :=
  (s1.val.zip s2.val).countP (fun q => p q.1 q.2)

def numXY (s1 s2 : Slice Std.U8) : ℕ :=
  countPairs (fun a b => a.val == 120 && b.val == 121) s1 s2

def numYX (s1 s2 : Slice Std.U8) : ℕ :=
  countPairs (fun a b => a.val == 121 && b.val == 120) s1 s2

def numX (s : Slice Std.U8) : ℕ :=
  s.val.countP (fun b => b.val == 120)

def expectedResult (s1 s2 : Slice Std.U8) : ℤ :=
  if (numXY s1 s2 + numYX s1 s2) % 2 = 1 then -1
  else (((numXY s1 s2) / 2 + (numYX s1 s2) / 2 + 2 * ((numXY s1 s2) % 2) : ℕ) : ℤ)

def aligned (s1 s2 : Slice Std.U8) : Prop :=
  ∀ (i : ℕ), i < s1.val.length → s1.val[i]? = s2.val[i]?

def swapAt (st : List Std.U8 × List Std.U8) (i j : ℕ) : List Std.U8 × List Std.U8 :=
  if h : i < st.1.length ∧ j < st.2.length then
    (st.1.set i (st.2[j]'h.2), st.2.set j (st.1[i]'h.1))
  else st

def applySwaps (st : List Std.U8 × List Std.U8) :
    List (ℕ × ℕ) → List Std.U8 × List Std.U8
  | [] => st
  | q :: qs => applySwaps (swapAt st q.1 q.2) qs

def Allowed (n : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | q :: qs => q.1 < n ∧ q.2 < n ∧ Allowed n qs

def SwapsToEqual (s1 s2 : Slice Std.U8) (seq : List (ℕ × ℕ)) : Prop :=
  Allowed s1.val.length seq ∧
    (applySwaps (s1.val, s2.val) seq).1 = (applySwaps (s1.val, s2.val) seq).2

def flipByte (b : Std.U8) : Std.U8 := if b.val = 120 then byteY else byteX

def mkSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Std.Usize.max then
    ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩
  else Slice.new Std.U8

/-- Let n = len(s1). Let A be the number of indices i with 0 <= i < n such that s1[i] = 120 ('x') and s2[i] = 121 ('y'). Let B be the number of indices i with 0 <= i < n such that s1[i] = 121 ('y') and s2[i] = 120 ('x'). The function returns a result r, and r is the minimum number of allowed swaps (each swap exchanges s1[i] and s2[j] for some 0 <= i,j < n; positions may be equal) needed to make s1 and s2 equal, or -1 if no sequence of allowed swaps can make them equal. Equivalently, if A+B is odd then r = -1; otherwise r = floor(A/2) + floor(B/2) + 2*(A mod 2), where A mod 2 is 0 or 1.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_1 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∃ r : Std.I64,
      minimum_swap s1 s2 = ok r ∧
      r.val = expectedResult s1 s2 ∧
      (r.val = -1 ↔ ∀ seq : List (ℕ × ℕ), ¬ SwapsToEqual s1 s2 seq) ∧
      (0 ≤ r.val →
        (∃ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq ∧ (seq.length : ℤ) = r.val) ∧
        ∀ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq → r.val ≤ (seq.length : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∃ r : Std.I64,
      minimum_swap s1 s2 = ok r ∧
      r.val = expectedResult s1 s2 ∧
      (r.val = -1 ↔ ∀ seq : List (ℕ × ℕ), ¬ SwapsToEqual s1 s2 seq) ∧
      (0 ≤ r.val →
        (∃ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq ∧ (seq.length : ℤ) = r.val) ∧
        ∀ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq → r.val ≤ (seq.length : ℤ))) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_2 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∃ r : Std.I64, minimum_swap s1 s2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∃ r : Std.I64, minimum_swap s1 s2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= len(s1).
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_3 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (s1.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (s1.val.length : ℤ))) := by
  sorry

/-- Let T be the total number of bytes equal to 120 ('x') among all bytes of s1 and s2. The function returns -1 if and only if T is odd.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_4 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r →
      (r.val = -1 ↔ Odd (numX s1 + numX s2)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r →
      (r.val = -1 ↔ Odd (numX s1 + numX s2))) := by
  sorry

/-- The function returns 0 if and only if for every i with 0 <= i < len(s1), s1[i] = s2[i].
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_5 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r →
      (r.val = 0 ↔ aligned s1 s2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r →
      (r.val = 0 ↔ aligned s1 s2)) := by
  sorry

/-- The function returns a result r on inputs (s1,s2), and when called on inputs (s2,s1) it returns the same result r.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_6 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∃ r : Std.I64, minimum_swap s1 s2 = ok r ∧ minimum_swap s2 s1 = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∃ r : Std.I64, minimum_swap s1 s2 = ok r ∧ minimum_swap s2 s1 = ok r) := by
  sorry

/-- Define s1' and s2' by s1'[i] = 121 if s1[i] = 120, and s1'[i] = 120 if s1[i] = 121, and similarly s2'[i] = 121 if s2[i] = 120, and s2'[i] = 120 if s2[i] = 121, for every 0 <= i < len(s1). The value returned by minimum_swap(s1',s2') equals the value returned by minimum_swap(s1,s2).
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_7 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∃ r : Std.I64,
      minimum_swap s1 s2 = ok r ∧
      minimum_swap (mkSlice (s1.val.map flipByte)) (mkSlice (s2.val.map flipByte)) = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∃ r : Std.I64,
      minimum_swap s1 s2 = ok r ∧
      minimum_swap (mkSlice (s1.val.map flipByte)) (mkSlice (s2.val.map flipByte)) = ok r) := by
  sorry

/-- Let A(s1,s2) be the number of indices i with s1[i]=120 and s2[i]=121, and B(s1,s2) be the number with s1[i]=121 and s2[i]=120, with analogous definitions for (t1,t2). If A(s1,s2) = A(t1,t2) and B(s1,s2) = B(t1,t2), then the value returned by minimum_swap(s1,s2) equals the value returned by minimum_swap(t1,t2).
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and all bytes of s1 and s2 are 120 ('x') or 121 ('y'); also len(t1) = len(t2), 1 <= len(t1) <= 1000, and all bytes of t1 and t2 are 120 ('x') or 121 ('y'). -/
theorem spec_8 (s1 s2 t1 t2 : Slice Std.U8)
    (hlen1 : s1.val.length = s2.val.length)
    (hpos1 : 1 ≤ s1.val.length)
    (hsize1 : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY)
    (hlen2 : t1.val.length = t2.val.length)
    (hpos2 : 1 ≤ t1.val.length)
    (hsize2 : t1.val.length ≤ 1000)
    (ht1 : ∀ (i : ℕ) (hi : i < t1.val.length), t1.val[i]'hi = byteX ∨ t1.val[i]'hi = byteY)
    (ht2 : ∀ (i : ℕ) (hi : i < t2.val.length), t2.val[i]'hi = byteX ∨ t2.val[i]'hi = byteY)
    (hA : numXY s1 s2 = numXY t1 t2)
    (hB : numYX s1 s2 = numYX t1 t2) :
    ∃ r : Std.I64, minimum_swap s1 s2 = ok r ∧ minimum_swap t1 t2 = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s1 s2 t1 t2 : Slice Std.U8)
    (hlen1 : s1.val.length = s2.val.length)
    (hpos1 : 1 ≤ s1.val.length)
    (hsize1 : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY)
    (hlen2 : t1.val.length = t2.val.length)
    (hpos2 : 1 ≤ t1.val.length)
    (hsize2 : t1.val.length ≤ 1000)
    (ht1 : ∀ (i : ℕ) (hi : i < t1.val.length), t1.val[i]'hi = byteX ∨ t1.val[i]'hi = byteY)
    (ht2 : ∀ (i : ℕ) (hi : i < t2.val.length), t2.val[i]'hi = byteX ∨ t2.val[i]'hi = byteY)
    (hA : numXY s1 s2 = numXY t1 t2)
    (hB : numYX s1 s2 = numYX t1 t2), ∃ r : Std.I64, minimum_swap s1 s2 = ok r ∧ minimum_swap t1 t2 = ok r) := by
  sorry

/-- For every c in {120 ('x'), 121 ('y')}, let s1' be the slice obtained by appending c to s1, and s2' be the slice obtained by appending c to s2. The value returned by minimum_swap(s1',s2') equals the value returned by minimum_swap(s1,s2).
  Preconditions: len(s1) = len(s2), 1 <= len(s1) < 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_9 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length < 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY)
    (c : Std.U8) (hc : c = byteX ∨ c = byteY) :
    ∃ r : Std.I64,
      minimum_swap s1 s2 = ok r ∧
      minimum_swap (mkSlice (s1.val ++ [c])) (mkSlice (s2.val ++ [c])) = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length < 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY)
    (c : Std.U8) (hc : c = byteX ∨ c = byteY), ∃ r : Std.I64,
      minimum_swap s1 s2 = ok r ∧
      minimum_swap (mkSlice (s1.val ++ [c])) (mkSlice (s2.val ++ [c])) = ok r) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists a finite sequence of exactly r allowed swaps that transforms the input strings into two equal strings.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_10 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      ∃ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq ∧ (seq.length : ℤ) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      ∃ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq ∧ (seq.length : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there is no finite sequence of fewer than r allowed swaps that transforms the input strings into two equal strings.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_11 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      ∀ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq → r.val ≤ (seq.length : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      ∀ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq → r.val ≤ (seq.length : ℤ)) := by
  sorry

/-- Whenever the function returns -1, there is no finite sequence of allowed swaps that transforms the input strings into two equal strings.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_12 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r → r.val = -1 →
      ¬ ∃ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r → r.val = -1 →
      ¬ ∃ seq : List (ℕ × ℕ), SwapsToEqual s1 s2 seq) := by
  sorry

/-- Let A be the number of indices i with 0 <= i < len(s1) such that s1[i]=120 ('x') and s2[i]=121 ('y'), and B be the number with s1[i]=121 ('y') and s2[i]=120 ('x'). Whenever the function returns a result r with r >= 0, 2*r >= A+B.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_13 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      2 * r.val ≥ ((numXY s1 s2 + numYX s1 s2 : ℕ) : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      2 * r.val ≥ ((numXY s1 s2 + numYX s1 s2 : ℕ) : ℤ)) := by
  sorry

/-- Let A be the number of indices i with 0 <= i < len(s1) such that s1[i]=120 ('x') and s2[i]=121 ('y'), and B be the number with s1[i]=121 ('y') and s2[i]=120 ('x'). Whenever the function returns a result r with r >= 0, r <= A+B.
  Preconditions: len(s1) = len(s2), 1 <= len(s1) <= 1000, and for every i with 0 <= i < len(s1), s1[i] is 120 ('x') or 121 ('y'), and s2[i] is 120 ('x') or 121 ('y'). -/
theorem spec_14 (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY) :
    ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      r.val ≤ ((numXY s1 s2 + numYX s1 s2 : ℕ) : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen : s1.val.length = s2.val.length)
    (hpos : 1 ≤ s1.val.length)
    (hsize : s1.val.length ≤ 1000)
    (hx1 : ∀ (i : ℕ) (hi : i < s1.val.length), s1.val[i]'hi = byteX ∨ s1.val[i]'hi = byteY)
    (hx2 : ∀ (i : ℕ) (hi : i < s2.val.length), s2.val[i]'hi = byteX ∨ s2.val[i]'hi = byteY), ∀ r : Std.I64, minimum_swap s1 s2 = ok r → 0 ≤ r.val →
      r.val ≤ ((numXY s1 s2 + numYX s1 s2 : ℕ) : ℤ)) := by
  sorry

end AegisSpec.MinimumSwap
