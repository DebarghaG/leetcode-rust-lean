import Aegis.MaximumScore.Code.Funs

/-!
# Specifications of `Aegis.MaximumScore.maximum_score`

LeetCode problem `maximum-score-from-removing-stones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumScore (maximum_score)

  namespace AegisSpec.MaximumScore

  def max3 (x y z : Int) : Int := max x (max y z)

  def floorHalf (S : Int) : Int := S / 2

  def sortedValues (x y z : Int) : List Int := List.insertionSort (· ≤ ·) [x, y, z]

  def secondLargest (x y z : Int) : Int := (sortedValues x y z).getD 1 0

  structure Piles where

    p1 : Int

    p2 : Int

    p3 : Int
  deriving DecidableEq, Repr

  def initialState (a b c : Std.I64) : Piles := ⟨a.val, b.val, c.val⟩

  def Piles.nonemptyCount (s : Piles) : Nat :=
    (if 0 < s.p1 then 1 else 0) + (if 0 < s.p2 then 1 else 0)
      + (if 0 < s.p3 then 1 else 0)

  def Piles.terminal (s : Piles) : Prop := s.nonemptyCount < 2

  def Piles.Step (s t : Piles) : Prop :=
    (1 ≤ s.p1 ∧ 1 ≤ s.p2 ∧ t = ⟨s.p1 - 1, s.p2 - 1, s.p3⟩)
  ∨ (1 ≤ s.p1 ∧ 1 ≤ s.p3 ∧ t = ⟨s.p1 - 1, s.p2, s.p3 - 1⟩)
  ∨ (1 ≤ s.p2 ∧ 1 ≤ s.p3 ∧ t = ⟨s.p1, s.p2 - 1, s.p3 - 1⟩)

  def Reachable (s : Piles) : Nat → Piles → Prop
    | 0, t => t = s
    | n + 1, t => ∃ u, Reachable s n u ∧ u.Step t

  /-- Let S = a + b + c and M = max(a, b, c). The function returns a result r (so it does not fail) and r = min(floor(S/2), S - M), where floor(S/2) is the greatest integer k with 2*k <= S.
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_1 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000) :
      ∃ r : Std.I64, maximum_score a b c = .ok r
        ∧ r.val = min (floorHalf (a.val + b.val + c.val))
            (a.val + b.val + c.val - max3 a.val b.val c.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000), ∃ r : Std.I64, maximum_score a b c = Result.ok r
          ∧ r.val = min (floorHalf (a.val + b.val + c.val))
              (a.val + b.val + c.val - max3 a.val b.val c.val)) := by
    sorry

  /-- For every valid a, b, c, the function returns some result r; in particular, evaluation of maximum_score does not overflow, panic, or access out of bounds.
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_2 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000) :
      ∃ r : Std.I64, maximum_score a b c = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000), ∃ r : Std.I64, maximum_score a b c = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the second largest of a, b, c, i.e. the middle value after sorting a, b, c in nondecreasing order.
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_3 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
      (r : Std.I64) (hr : maximum_score a b c = .ok r) :
      secondLargest a.val b.val c.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
        (r : Std.I64) (hr : maximum_score a b c = Result.ok r), secondLargest a.val b.val c.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 2*r <= a + b + c.
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_4 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
      (r : Std.I64) (hr : maximum_score a b c = .ok r) :
      2 * r.val ≤ a.val + b.val + c.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
        (r : Std.I64) (hr : maximum_score a b c = Result.ok r), 2 * r.val ≤ a.val + b.val + c.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= (a + b + c) - max(a, b, c).
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_5 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
      (r : Std.I64) (hr : maximum_score a b c = .ok r) :
      r.val ≤ a.val + b.val + c.val - max3 a.val b.val c.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
        (r : Std.I64) (hr : maximum_score a b c = Result.ok r), r.val ≤ a.val + b.val + c.val - max3 a.val b.val c.val) := by
    sorry

  /-- The function returns a result r, and if max(a, b, c) <= (a + b + c) - max(a, b, c), then r = floor((a + b + c)/2).
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_6 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000) :
      ∃ r : Std.I64, maximum_score a b c = .ok r
        ∧ (max3 a.val b.val c.val ≤ a.val + b.val + c.val - max3 a.val b.val c.val
            → r.val = floorHalf (a.val + b.val + c.val)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000), ∃ r : Std.I64, maximum_score a b c = Result.ok r
          ∧ (max3 a.val b.val c.val ≤ a.val + b.val + c.val - max3 a.val b.val c.val
              → r.val = floorHalf (a.val + b.val + c.val))) := by
    sorry

  /-- The function returns a result r, and if max(a, b, c) >= (a + b + c) - max(a, b, c), then r = (a + b + c) - max(a, b, c).
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_7 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000) :
      ∃ r : Std.I64, maximum_score a b c = .ok r
        ∧ (max3 a.val b.val c.val ≥ a.val + b.val + c.val - max3 a.val b.val c.val
            → r.val = a.val + b.val + c.val - max3 a.val b.val c.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000), ∃ r : Std.I64, maximum_score a b c = Result.ok r
          ∧ (max3 a.val b.val c.val ≥ a.val + b.val + c.val - max3 a.val b.val c.val
              → r.val = a.val + b.val + c.val - max3 a.val b.val c.val)) := by
    sorry

  /-- For every valid a, b, c and every permutation (x, y, z) of (a, b, c), the result returned by maximum_score(a, b, c) equals the result returned by maximum_score(x, y, z).
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_8 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
      (x y z : Std.I64)
      (hperm : List.Perm [x.val, y.val, z.val] [a.val, b.val, c.val]) :
      maximum_score x y z = maximum_score a b c := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
        (x y z : Std.I64)
        (hperm : List.Perm [x.val, y.val, z.val] [a.val, b.val, c.val]), maximum_score x y z = maximum_score a b c) := by
    sorry

  /-- If r is the result returned by maximum_score(a, b, c) and r' is the result returned by maximum_score(a', b', c'), then r <= r'.
    Preconditions: a, b, c are integer values satisfying 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000; additionally a', b', c' are integers satisfying 1 <= a' <= 100000, 1 <= b' <= 100000, 1 <= c' <= 100000, with a <= a', b <= b', and c <= c'. -/
  theorem spec_9 (a b c a' b' c' : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
      (ha'1 : 1 ≤ a'.val) (ha'2 : a'.val ≤ 100000)
      (hb'1 : 1 ≤ b'.val) (hb'2 : b'.val ≤ 100000)
      (hc'1 : 1 ≤ c'.val) (hc'2 : c'.val ≤ 100000)
      (hab : a.val ≤ a'.val) (hbc : b.val ≤ b'.val) (hcc : c.val ≤ c'.val)
      (r r' : Std.I64) (hr : maximum_score a b c = .ok r)
      (hr' : maximum_score a' b' c' = .ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (a b c a' b' c' : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
        (ha'1 : 1 ≤ a'.val) (ha'2 : a'.val ≤ 100000)
        (hb'1 : 1 ≤ b'.val) (hb'2 : b'.val ≤ 100000)
        (hc'1 : 1 ≤ c'.val) (hc'2 : c'.val ≤ 100000)
        (hab : a.val ≤ a'.val) (hbc : b.val ≤ b'.val) (hcc : c.val ≤ c'.val)
        (r r' : Std.I64) (hr : maximum_score a b c = Result.ok r)
        (hr' : maximum_score a' b' c' = Result.ok r'), r.val ≤ r'.val) := by
    sorry

  /-- The function returns a result r, and there exists a sequence of exactly r legal moves starting from (a, b, c) such that afterward fewer than two piles are nonempty. A legal move chooses two distinct currently nonempty piles and subtracts 1 from each; the score is the number of moves.
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_10 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000) :
      ∃ r : Std.I64, maximum_score a b c = .ok r
        ∧ ∃ (n : Nat) (s : Piles), (n : Int) = r.val
            ∧ Reachable (initialState a b c) n s ∧ s.terminal := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000), ∃ r : Std.I64, maximum_score a b c = Result.ok r
          ∧ ∃ (n : Nat) (s : Piles), (n : Int) = r.val
              ∧ Reachable (initialState a b c) n s ∧ s.terminal) := by
    sorry

  /-- For every sequence of legal moves starting from (a, b, c) that at each step chooses two distinct nonempty piles and subtracts 1 from each, and that continues until fewer than two piles are nonempty, the number of moves is at most r, where r is the result returned by maximum_score(a, b, c).
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_11 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
      (r : Std.I64) (hr : maximum_score a b c = .ok r) :
      ∀ (n : Nat) (s : Piles), Reachable (initialState a b c) n s → s.terminal
        → (n : Int) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000)
        (r : Std.I64) (hr : maximum_score a b c = Result.ok r), ∀ (n : Nat) (s : Piles), Reachable (initialState a b c) n s → s.terminal
          → (n : Int) ≤ r.val) := by
    sorry

  /-- Let M = max(a, b, c). If M > (a + b + c) - M, then in every complete play that attains the maximum score r, the two piles other than the unique largest pile are emptied and the unique largest pile is left with 2*M - (a + b + c) stones.
    Preconditions: a, b, c are the integer values of the I64 parameters and satisfy 1 <= a <= 100000, 1 <= b <= 100000, 1 <= c <= 100000. -/
  theorem spec_12 (a b c : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
      (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000) :
      let M := max3 a.val b.val c.val
      let S := a.val + b.val + c.val
      M > S - M
        → ∀ (r : Std.I64) (n : Nat) (s : Piles), maximum_score a b c = .ok r
            → (n : Int) = r.val → Reachable (initialState a b c) n s → s.terminal
            → (a.val = M → s = ⟨2 * M - S, 0, 0⟩)
              ∧ (b.val = M → s = ⟨0, 2 * M - S, 0⟩)
              ∧ (c.val = M → s = ⟨0, 0, 2 * M - S⟩) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 100000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 100000)
        (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100000), let M := max3 a.val b.val c.val
        let S := a.val + b.val + c.val
        M > S - M
          → ∀ (r : Std.I64) (n : Nat) (s : Piles), maximum_score a b c = Result.ok r
              → (n : Int) = r.val → Reachable (initialState a b c) n s → s.terminal
              → (a.val = M → s = ⟨2 * M - S, 0, 0⟩)
                ∧ (b.val = M → s = ⟨0, 2 * M - S, 0⟩)
                ∧ (c.val = M → s = ⟨0, 0, 2 * M - S⟩)) := by
    sorry

  end AegisSpec.MaximumScore
