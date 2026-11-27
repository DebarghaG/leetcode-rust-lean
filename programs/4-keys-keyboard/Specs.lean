import Aegis.MaxA.Code.Funs

/-!
# Specifications of `Aegis.MaxA.max_a`

LeetCode problem `4-keys-keyboard`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxA

def copyBest (m : Nat) (prev : List Nat) : Nat :=
  (List.range (m - 2)).foldr (fun k acc => max (prev.getD k 0 * (m - k - 1)) acc) 0

def nextM (m : Nat) (prev : List Nat) : Nat :=
  if m = 0 then 0
  else max (prev.getD (m - 1) 0 + 1) (copyBest m prev)

def Mvals : Nat → List Nat
  | 0 => []
  | m + 1 => Mvals m ++ [nextM m (Mvals m)]

def M (m : Nat) : Nat := (Mvals (m + 1)).getD m 0

inductive Key where

  | a : Key

  | ctrlA : Key

  | ctrlC : Key

  | ctrlV : Key
  deriving DecidableEq, Repr

abbrev EditorState := Nat × Nat

def Key.step (k : Key) (st : EditorState) : EditorState :=
  match k with
  | .a => (st.1 + 1, st.2)
  | .ctrlA => st
  | .ctrlC => (st.1, st.1)
  | .ctrlV => (st.1 + st.2, st.2)

def run : List Key → EditorState → EditorState
  | [], st => st
  | k :: ks, st => run ks (Key.step k st)

def ctrlCPrecededB : List Key → Bool
  | [] => true
  | [_] => true
  | k :: k' :: rest => (k' != Key.ctrlC || k == Key.ctrlA) && ctrlCPrecededB (k' :: rest)

def CtrlCPreceded (ks : List Key) : Prop := ctrlCPrecededB ks = true

def allKeys : List Key := [Key.a, Key.ctrlA, Key.ctrlC, Key.ctrlV]

def seqsOfLen : Nat → List (List Key)
  | 0 => [[]]
  | len + 1 => (seqsOfLen len).flatMap (fun s => allKeys.map (fun k => s ++ [k]))

def maxScreen (n : Nat) : Nat :=
  ((List.range (n + 1)).flatMap seqsOfLen).foldr
    (fun ks acc => if ctrlCPrecededB ks then max (run ks (0, 0)).1 acc else acc) 0

def succI64 (n : Std.I64) : Std.I64 := Std.I64.wrapping_add n 1#i64

/-- Let M be the function on nonnegative integers defined by M(0)=0 and, for every integer m>=1, M(m) = max( M(m-1)+1, max{ M(k)*(m-k-1) | 0 <= k <= m-3 } ), where a maximum over an empty index set is 0. The function returns Ok r, where r is the integer value of the returned I64, and r = M(n). This value is exactly the largest number of 'A' characters that can be on the screen after at most n key presses by a sequence in which every Ctrl-C is immediately preceded by a Ctrl-A, under the rules: initially the screen and buffer are empty; A appends one 'A'; Ctrl-A selects the whole screen; Ctrl-C copies the selected screen to the buffer; Ctrl-V appends the buffer to the screen.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 50. -/
theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50) :
    ∃ r : Std.I64,
      Aegis.MaxA.max_a n = ok r ∧ r.val = (M n.val.toNat : ℤ) ∧
        (M n.val.toNat : ℤ) = (maxScreen n.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50), ∃ r : Std.I64,
      Aegis.MaxA.max_a n = ok r ∧ r.val = (M n.val.toNat : ℤ) ∧
        (M n.val.toNat : ℤ) = (maxScreen n.val.toNat : ℤ)) := by
  sorry

/-- The function returns Ok r for some I64 value r; it does not fail (no overflow, no out-of-bounds access, no panic) for any n in this range.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 50. -/
theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50) :
    ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50), ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r) := by
  sorry

/-- Whenever the function returns Ok r, the integer value r satisfies r >= n.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 50. -/
theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50) :
    ∀ r : Std.I64, Aegis.MaxA.max_a n = ok r → n.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50), ∀ r : Std.I64, Aegis.MaxA.max_a n = ok r → n.val ≤ r.val) := by
  sorry

/-- Whenever the function returns Ok r, the integer value r satisfies r <= 2^n, where 2^n is exponentiation with nonnegative exponent n.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 50. -/
theorem spec_4 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50) :
    ∀ r : Std.I64, Aegis.MaxA.max_a n = ok r → r.val ≤ (2 : ℤ) ^ n.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50), ∀ r : Std.I64, Aegis.MaxA.max_a n = ok r → r.val ≤ (2 : ℤ) ^ n.val.toNat) := by
  sorry

/-- The function returns Ok r, where r is the integer value, and r = n.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 6. -/
theorem spec_5 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 6) :
    ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 6), ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = n.val) := by
  sorry

/-- The function returns Ok r, where r is the integer value, and r = 9.
  Preconditions: Let n be the integer value of the I64 parameter, with n = 7. -/
theorem spec_6 (n : Std.I64) (h1 : n.val = 7) :
    ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = 9 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (h1 : n.val = 7), ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = 9) := by
  sorry

/-- The function returns Ok r, where r is the integer value, and r = 81.
  Preconditions: Let n be the integer value of the I64 parameter, with n = 15. -/
theorem spec_7 (n : Std.I64) (h1 : n.val = 15) :
    ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = 81 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (h1 : n.val = 15), ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = 81) := by
  sorry

/-- The function returns Ok r, where r is the integer value, and r = 324.
  Preconditions: Let n be the integer value of the I64 parameter, with n = 20. -/
theorem spec_8 (n : Std.I64) (h1 : n.val = 20) :
    ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = 324 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (h1 : n.val = 20), ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ r.val = 324) := by
  sorry

/-- If the function returns Ok r for input n and Ok s for input n+1, then the integer values satisfy r <= s.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n < 50. -/
theorem spec_9 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 50) :
    ∀ r s : Std.I64,
      Aegis.MaxA.max_a n = ok r → Aegis.MaxA.max_a (succI64 n) = ok s → r.val ≤ s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 50), ∀ r s : Std.I64,
      Aegis.MaxA.max_a n = ok r → Aegis.MaxA.max_a (succI64 n) = ok s → r.val ≤ s.val) := by
  sorry

/-- If the function returns Ok r for input n and Ok s for input n+1, then the integer values satisfy s >= r + 1.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n < 50. -/
theorem spec_10 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 50) :
    ∀ r s : Std.I64,
      Aegis.MaxA.max_a n = ok r → Aegis.MaxA.max_a (succI64 n) = ok s → r.val + 1 ≤ s.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 50), ∀ r s : Std.I64,
      Aegis.MaxA.max_a n = ok r → Aegis.MaxA.max_a (succI64 n) = ok s → r.val + 1 ≤ s.val) := by
  sorry

/-- The function returns Ok r, where r is the integer value, and r > n.
  Preconditions: Let n be the integer value of the I64 parameter, with 7 <= n <= 50. -/
theorem spec_11 (n : Std.I64) (h1 : 7 ≤ n.val) (h2 : n.val ≤ 50) :
    ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ n.val < r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (h1 : 7 ≤ n.val) (h2 : n.val ≤ 50), ∃ r : Std.I64, Aegis.MaxA.max_a n = ok r ∧ n.val < r.val) := by
  sorry

/-- The function returns Ok r, where r is the integer value, and there exists a sequence of at most n key presses, in which every Ctrl-C is immediately preceded by a Ctrl-A, that starts with an empty screen and an empty buffer and ends with exactly r 'A' characters on the screen. The permitted keys are A (append one 'A'), Ctrl-A (select the whole screen), Ctrl-C (copy the selected screen to the buffer), and Ctrl-V (append the buffer to the screen).
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 50. -/
theorem spec_12 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50) :
    ∃ r : Std.I64,
      Aegis.MaxA.max_a n = ok r ∧
        ∃ ks : List Key,
          ks.length ≤ n.val.toNat ∧ CtrlCPreceded ks ∧ ((run ks (0, 0)).1 : ℤ) = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50), ∃ r : Std.I64,
      Aegis.MaxA.max_a n = ok r ∧
        ∃ ks : List Key,
          ks.length ≤ n.val.toNat ∧ CtrlCPreceded ks ∧ ((run ks (0, 0)).1 : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns Ok r, for every sequence of at most n key presses using the four keys A, Ctrl-A, Ctrl-C, Ctrl-V, in which every Ctrl-C is immediately preceded by a Ctrl-A, starting with an empty screen and an empty buffer, the sequence leaves at most r 'A' characters on the screen. The effects are: A appends one 'A'; Ctrl-A selects the whole screen; Ctrl-C copies the selected screen to the buffer; Ctrl-V appends the buffer to the screen.
  Preconditions: Let n be the integer value of the I64 parameter, with 1 <= n <= 50. -/
theorem spec_13 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50) :
    ∀ r : Std.I64,
      Aegis.MaxA.max_a n = ok r →
        ∀ ks : List Key,
          ks.length ≤ n.val.toNat → CtrlCPreceded ks → ((run ks (0, 0)).1 : ℤ) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 50), ∀ r : Std.I64,
      Aegis.MaxA.max_a n = ok r →
        ∀ ks : List Key,
          ks.length ≤ n.val.toNat → CtrlCPreceded ks → ((run ks (0, 0)).1 : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.MaxA
