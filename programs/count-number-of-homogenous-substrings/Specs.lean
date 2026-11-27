import Aegis.CountHomogenous.Code.Funs

/-!
# Specifications of `Aegis.CountHomogenous.count_homogenous`

LeetCode problem `count-number-of-homogenous-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountHomogenous

def bytesOf (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

def isLowerByte (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

def ValidInput (s : Slice U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100000 ∧ ∀ b ∈ bytesOf s, isLowerByte b

def HomogWindow (l : List Nat) (i j : Nat) : Prop :=
  i ≤ j ∧ j < l.length ∧ ∀ k ∈ Finset.Icc i j, l.getD k 0 = l.getD i 0

instance (l : List Nat) (i j : Nat) : Decidable (HomogWindow l i j) := by
  unfold HomogWindow
  infer_instance

def homogCount (s : Slice U8) : Nat :=
  (((Finset.range s.val.length).product (Finset.range s.val.length)).filter
    (fun p : Nat × Nat => HomogWindow (bytesOf s) p.1 p.2)).card

def runLengthsFrom (l : List Nat) (x c : Nat) : List Nat :=
  match l with
  | [] => [c]
  | y :: ys => if y = x then runLengthsFrom ys x (c + 1) else c :: runLengthsFrom ys y 1

def runLengths : List Nat → List Nat
  | [] => []
  | x :: xs => runLengthsFrom xs x 1

def runTriSum (l : List Nat) : Nat :=
  (runLengths l).map (fun L => L * (L + 1) / 2) |>.sum

/-- Whenever count_homogenous(s) returns a result r, r equals the number of pairs (i,j) such that 0 <= i <= j < len(s) and s[k] = s[i] for every k with i <= k <= j, reduced modulo 1000000007. Equivalently, r is the number of homogeneous contiguous substrings of s modulo 1000000007.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000 and, for every i with 0 <= i < len(s), s[i] is a lowercase ASCII byte (97 <= s[i] <= 122). -/
theorem spec_1 (s : Slice U8) (h : ValidInput s) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((homogCount s : Nat) : Int) % 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((homogCount s : Nat) : Int) % 1000000007) := by
  sorry

/-- The function returns a result r (it does not fail) for every such s.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000 and, for every i with 0 <= i < len(s), s[i] is a lowercase ASCII byte (97 <= s[i] <= 122). -/
theorem spec_2 (s : Slice U8) (h : ValidInput s) :
    ∃ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s), ∃ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < 1000000007.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000 and, for every i with 0 <= i < len(s), s[i] is a lowercase ASCII byte (97 <= s[i] <= 122). -/
theorem spec_3 (s : Slice U8) (h : ValidInput s) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Whenever the function returns a result r, r = N mod 1000000007 and len(s) <= N <= len(s)*(len(s)+1)/2.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000 and, for every i with 0 <= i < len(s), s[i] is a lowercase ASCII byte (97 <= s[i] <= 122). Let N be the exact number of homogeneous contiguous substrings of s. -/
theorem spec_4 (s : Slice U8) (h : ValidInput s) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((homogCount s : Nat) : Int) % 1000000007 ∧
        s.val.length ≤ homogCount s ∧
        homogCount s ≤ s.val.length * (s.val.length + 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((homogCount s : Nat) : Int) % 1000000007 ∧
        s.val.length ≤ homogCount s ∧
        homogCount s ≤ s.val.length * (s.val.length + 1) / 2) := by
  sorry

/-- Let L_1, L_2, ..., L_m be the lengths of the maximal contiguous nonempty runs of equal bytes in s, in their left-to-right order. Whenever the function returns a result r, r = (sum_{t=1}^m L_t*(L_t+1)/2) mod 1000000007.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000 and, for every i with 0 <= i < len(s), s[i] is a lowercase ASCII byte (97 <= s[i] <= 122). -/
theorem spec_5 (s : Slice U8) (h : ValidInput s) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((runTriSum (bytesOf s) : Nat) : Int) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((runTriSum (bytesOf s) : Nat) : Int) % 1000000007) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: len(s) = 1 and s[0] is a lowercase ASCII byte (97 <= s[0] <= 122). -/
theorem spec_6 (s : Slice U8) (hlen : s.val.length = 1)
    (h0 : isLowerByte ((bytesOf s).getD 0 0)) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (hlen : s.val.length = 1)
    (h0 : isLowerByte ((bytesOf s).getD 0 0)), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = (len(s)*(len(s)+1)/2) mod 1000000007.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000, every byte is a lowercase ASCII byte (97 <= s[i] <= 122), and s[i] = s[0] for every i with 0 <= i < len(s). -/
theorem spec_7 (s : Slice U8) (h : ValidInput s)
    (hconst : ∀ i, i < s.val.length → (bytesOf s).getD i 0 = (bytesOf s).getD 0 0) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) % 1000000007 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s)
    (hconst : ∀ i, i < s.val.length → (bytesOf s).getD i 0 = (bytesOf s).getD 0 0), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) % 1000000007) := by
  sorry

/-- Whenever the function returns a result r, r = len(s).
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000, every byte is a lowercase ASCII byte (97 <= s[i] <= 122), and for every i with 0 <= i < len(s)-1, s[i] != s[i+1]. -/
theorem spec_8 (s : Slice U8) (h : ValidInput s)
    (hadj : ∀ i, i + 1 < s.val.length → (bytesOf s).getD i 0 ≠ (bytesOf s).getD (i + 1) 0) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = (s.val.length : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s)
    (hadj : ∀ i, i + 1 < s.val.length → (bytesOf s).getD i 0 ≠ (bytesOf s).getD (i + 1) 0), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      r.val = (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 13.
  Preconditions: s is exactly the ASCII byte sequence "abbcccaa" (length 8). -/
theorem spec_9 (s : Slice U8) (hs : bytesOf s = [97, 98, 98, 99, 99, 99, 97, 97]) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 13 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (hs : bytesOf s = [97, 98, 98, 99, 99, 99, 97, 97]), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 13) := by
  sorry

/-- Whenever count_homogenous(s) returns a result r, r = 46.
  Preconditions: s is exactly the ASCII byte sequence aabbccddeeefffggghhhiiii, which has length 24 (all bytes are lowercase ASCII letters). -/
theorem spec_10 (s : Slice U8)
    (hs : bytesOf s =
      [97, 97, 98, 98, 99, 99, 100, 100, 101, 101, 101, 102, 102, 102, 103, 103, 103,
        104, 104, 104, 105, 105, 105, 105]) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 46 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hs : bytesOf s =
      [97, 97, 98, 98, 99, 99, 100, 100, 101, 101, 101, 102, 102, 102, 103, 103, 103,
        104, 104, 104, 105, 105, 105, 105]), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 46) := by
  sorry

/-- Whenever the function returns a result r, r = 2.
  Preconditions: s is exactly the ASCII byte sequence "xy" (length 2). -/
theorem spec_11 (s : Slice U8) (hs : bytesOf s = [120, 121]) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (hs : bytesOf s = [120, 121]), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, r = 49965.
  Preconditions: s is a byte slice with len(s) = 100000, every byte is a lowercase ASCII byte (97 <= s[i] <= 122), and s[i] = s[0] for every i with 0 <= i < len(s). -/
theorem spec_12 (s : Slice U8) (hlen : s.val.length = 100000)
    (hlower : ∀ b ∈ bytesOf s, isLowerByte b)
    (hconst : ∀ i, i < s.val.length → (bytesOf s).getD i 0 = (bytesOf s).getD 0 0) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 49965 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (hlen : s.val.length = 100000)
    (hlower : ∀ b ∈ bytesOf s, isLowerByte b)
    (hconst : ∀ i, i < s.val.length → (bytesOf s).getD i 0 = (bytesOf s).getD 0 0), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r → r.val = 49965) := by
  sorry

/-- Whenever count_homogenous(s) returns a result r, for every valid byte slice t with 1 <= len(t) <= 100000, lowercase ASCII bytes, and the same ordered sequence of maximal constant-run lengths as s, if count_homogenous(t) returns a result r', then r = r'.
  Preconditions: s is a byte slice with 1 <= len(s) <= 100000 and, for every i with 0 <= i < len(s), s[i] is a lowercase ASCII byte (97 <= s[i] <= 122). -/
theorem spec_13 (s : Slice U8) (h : ValidInput s) :
    ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      ∀ t : Slice U8, ValidInput t →
        runLengths (bytesOf t) = runLengths (bytesOf s) →
          ∀ r' : I64, Aegis.CountHomogenous.count_homogenous t = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (h : ValidInput s), ∀ r : I64, Aegis.CountHomogenous.count_homogenous s = ok r →
      ∀ t : Slice U8, ValidInput t →
        runLengths (bytesOf t) = runLengths (bytesOf s) →
          ∀ r' : I64, Aegis.CountHomogenous.count_homogenous t = ok r' → r = r') := by
  sorry

end AegisSpec.CountHomogenous
