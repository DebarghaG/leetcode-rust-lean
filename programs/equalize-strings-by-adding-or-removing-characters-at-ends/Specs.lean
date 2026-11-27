import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `equalize-strings-by-adding-or-removing-characters-at-ends`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def byteVals (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def AsciiLower (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

def CommonSubstr (a b : List Nat) (k : Nat) : Prop :=
  ∃ i j : Nat, i + k ≤ a.length ∧ j + k ≤ b.length ∧
    (a.drop i).take k = (b.drop j).take k

def IsLongestCommonSubstr (a b : List Nat) (L : Nat) : Prop :=
  CommonSubstr a b L ∧ ∀ k : Nat, CommonSubstr a b k → k ≤ L

def SubstringOf (a b : List Nat) : Prop :=
  ∃ i : Nat, i + a.length ≤ b.length ∧ (b.drop i).take a.length = a

def SameBytes (s t : Slice Std.U8) : Prop := s.val = t.val

def overlapFromResult (s t : Slice Std.U8) (r : Std.I64) : Int :=
  ((s.val.length : Int) + (t.val.length : Int) - r.val) / 2

def revSlice (s : Slice Std.U8) : Slice Std.U8 :=
  Slice.from s.val.reverse (by simp [List.length_reverse])

/-- The function returns a result r, and, with n = len(initial), m = len(target), and L defined as the largest natural number such that there exist indices i and j with 0 <= i, i + L <= n, 0 <= j, j + L <= m, and initial[i+t] = target[j+t] for every t with 0 <= t < L (the case L = 0 is allowed), the integer value of r is n + m - 2*L. Equivalently, r is the minimum number of single-character additions or removals at the beginning or end of initial needed to obtain target.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_1 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        ∃ L : Nat,
          IsLongestCommonSubstr (byteVals initial) (byteVals target) L ∧
            r.val = (initial.val.length : Int) + (target.val.length : Int) - 2 * (L : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        ∃ L : Nat,
          IsLongestCommonSubstr (byteVals initial) (byteVals target) L ∧
            r.val = (initial.val.length : Int) + (target.val.length : Int) - 2 * (L : Int)) := by
  sorry

/-- The function returns a result r and does not fail: no panic, out-of-bounds access, or 64-bit arithmetic overflow occurs.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_2 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations initial target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∃ r : Std.I64, Aegis.MinOperations.min_operations initial target = ok r) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r satisfies |len(initial) - len(target)| <= r <= len(initial) + len(target).
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_3 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        |(initial.val.length : Int) - (target.val.length : Int)| ≤ r.val ∧
          r.val ≤ (initial.val.length : Int) + (target.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        |(initial.val.length : Int) - (target.val.length : Int)| ≤ r.val ∧
          r.val ≤ (initial.val.length : Int) + (target.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists a natural number L with 0 <= L <= min(len(initial), len(target)) such that r = len(initial) + len(target) - 2*L; equivalently, len(initial) + len(target) - r is even and its half lies between 0 and min(len(initial), len(target)).
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_4 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∃ L : Nat,
          L ≤ min initial.val.length target.val.length ∧
            r.val = (initial.val.length : Int) + (target.val.length : Int) - 2 * (L : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∃ L : Nat,
          L ≤ min initial.val.length target.val.length ∧
            r.val = (initial.val.length : Int) + (target.val.length : Int) - 2 * (L : Int)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if len(initial) = len(target) and initial[i] = target[i] for every i with 0 <= i < len(initial).
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_5 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        (r.val = 0 ↔ SameBytes initial target) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        (r.val = 0 ↔ SameBytes initial target)) := by
  sorry

/-- The function returns a result r, and r = len(initial) + len(target) if and only if there is no byte value occurring in both initial and target, i.e. for every i with 0 <= i < len(initial) and every j with 0 <= j < len(target), initial[i] != target[j].
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_6 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        (r.val = (initial.val.length : Int) + (target.val.length : Int) ↔
          ∀ (i : Nat) (hi : i < initial.val.length)
            (j : Nat) (hj : j < target.val.length), initial.val[i] ≠ target.val[j]) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        (r.val = (initial.val.length : Int) + (target.val.length : Int) ↔
          ∀ (i : Nat) (hi : i < initial.val.length)
            (j : Nat) (hj : j < target.val.length), initial.val[i] ≠ target.val[j])) := by
  sorry

/-- The function returns a result r, and r = |len(initial) - len(target)| if and only if one of the two slices is a contiguous substring of the other: either there exists j with 0 <= j and j + len(target) <= len(initial) and initial[j+t] = target[t] for every t with 0 <= t < len(target), or there exists i with 0 <= i and i + len(initial) <= len(target) and target[i+t] = initial[t] for every t with 0 <= t < len(initial).
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_7 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        (r.val = |(initial.val.length : Int) - (target.val.length : Int)| ↔
          (SubstringOf (byteVals target) (byteVals initial) ∨
            SubstringOf (byteVals initial) (byteVals target))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∃ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r ∧
        (r.val = |(initial.val.length : Int) - (target.val.length : Int)| ↔
          (SubstringOf (byteVals target) (byteVals initial) ∨
            SubstringOf (byteVals initial) (byteVals target)))) := by
  sorry

/-- Whenever the function returns a result r, for every positive integer k and indices i and j such that 0 <= i, i + k <= len(initial), 0 <= j, j + k <= len(target), and initial[i+t] = target[j+t] for every t with 0 <= t < k, the integer value of r satisfies r <= len(initial) + len(target) - 2*k.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_8 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∀ k : Nat,
          1 ≤ k →
            CommonSubstr (byteVals initial) (byteVals target) k →
              r.val ≤
                (initial.val.length : Int) + (target.val.length : Int) - 2 * (k : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∀ k : Nat,
          1 ≤ k →
            CommonSubstr (byteVals initial) (byteVals target) k →
              r.val ≤
                (initial.val.length : Int) + (target.val.length : Int) - 2 * (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, letting L = (len(initial) + len(target) - r)/2 (which is a natural number for every returned r), there exist indices i and j such that 0 <= i, i + L <= len(initial), 0 <= j, j + L <= len(target), and initial[i+t] = target[j+t] for every t with 0 <= t < L.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_9 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∃ L : Nat,
          (L : Int) = overlapFromResult initial target r ∧
            CommonSubstr (byteVals initial) (byteVals target) L := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∃ L : Nat,
          (L : Int) = overlapFromResult initial target r ∧
            CommonSubstr (byteVals initial) (byteVals target) L) := by
  sorry

/-- Whenever the function returns a result r, letting L = (len(initial) + len(target) - r)/2, there is no common contiguous substring of initial and target of length greater than L: for every positive integer k and indices i and j with 0 <= i, i + k <= len(initial), 0 <= j, j + k <= len(target), and initial[i+t] = target[j+t] for every t with 0 <= t < k, we have k <= L.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_10 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∃ L : Nat,
          (L : Int) = overlapFromResult initial target r ∧
            ∀ k : Nat,
              1 ≤ k → CommonSubstr (byteVals initial) (byteVals target) k → k ≤ L := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        ∃ L : Nat,
          (L : Int) = overlapFromResult initial target r ∧
            ∀ k : Nat,
              1 ≤ k → CommonSubstr (byteVals initial) (byteVals target) k → k ≤ L) := by
  sorry

/-- For every pair of strings satisfying the preconditions, if the function returns r on (initial, target), then when it is invoked on the swapped arguments (target, initial) it also returns r.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_11 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        Aegis.MinOperations.min_operations target initial = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        Aegis.MinOperations.min_operations target initial = ok r) := by
  sorry

/-- Let revInitial be the slice of length len(initial) with revInitial[i] = initial[len(initial)-1-i] for 0 <= i < len(initial), and let revTarget be defined analogously from target. Whenever the function returns r on (initial, target), any invocation on (revInitial, revTarget) returns the same r.
  Preconditions: 1 <= len(initial) <= 1000 and 1 <= len(target) <= 1000; every byte of initial and target is an ASCII lowercase letter (code in 97..122 inclusive). -/
theorem spec_12 (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target) :
    ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        Aegis.MinOperations.min_operations (revSlice initial) (revSlice target) = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (initial target : Slice Std.U8)
    (h_initial_lower : 1 ≤ initial.val.length) (h_initial_upper : initial.val.length ≤ 1000)
    (h_target_lower : 1 ≤ target.val.length) (h_target_upper : target.val.length ≤ 1000)
    (h_initial_ascii : AsciiLower initial) (h_target_ascii : AsciiLower target), ∀ r : Std.I64,
      Aegis.MinOperations.min_operations initial target = ok r →
        Aegis.MinOperations.min_operations (revSlice initial) (revSlice target) = ok r) := by
  sorry

end AegisSpec.MinOperations
