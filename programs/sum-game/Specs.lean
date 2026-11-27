import Aegis.SumGame.Code.Funs

/-!
# Specifications of `Aegis.SumGame.sum_game`

LeetCode problem `sum-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumGame

def digitVal (c : U8) : Int :=
  if 48 ≤ c.val ∧ c.val ≤ 57 then (c.val : Int) - 48 else 0

def isQuestion (c : U8) : Bool := c.val == 63

def IsDigitOrQuestion (c : U8) : Prop :=
  (48 ≤ c.val ∧ c.val ≤ 57) ∨ c.val = 63

def windowSum (l : List U8) (lo hi : Nat) : Int :=
  ((l.drop lo).take (hi - lo)).foldr (fun c acc => digitVal c + acc) 0

def windowQCount (l : List U8) (lo hi : Nat) : Int :=
  (((l.drop lo).take (hi - lo)).filter isQuestion).length

def sumLeft (l : List U8) : Int := windowSum l 0 (l.length / 2)

def sumRight (l : List U8) : Int := windowSum l (l.length / 2) l.length

def qLeft (l : List U8) : Int := windowQCount l 0 (l.length / 2)

def qRight (l : List U8) : Int := windowQCount l (l.length / 2) l.length

/-- Let h = len(num)/2. Let SL = sum_{i=0}^{h-1} d(num[i]) and SR = sum_{i=h}^{len(num)-1} d(num[i]), where d(c)=c-48 if 48<=c<=57 and d(c)=0 otherwise. Let qL = count_{i=0}^{h-1}(num[i]=63) and qR = count_{i=h}^{len(num)-1}(num[i]=63). The function returns a result r (it does not fail), and r = true if and only if 2*(SL-SR) != 9*(qR-qL). Equivalently, r = true exactly when Alice has a winning strategy in the game, and r = false exactly when Bob has a winning strategy.
  Preconditions: len(num) is even, 2 <= len(num) <= 100000, and for every i with 0 <= i < len(num), num[i] is either an ASCII digit byte (48 <= num[i] <= 57) or the ASCII byte for '?' (num[i] = 63). -/
theorem spec_1 (num : Slice U8)
    (heven : num.val.length % 2 = 0)
    (hlower : 2 ≤ num.val.length)
    (hupper : num.val.length ≤ 100000)
    (hbytes : ∀ (i : Nat) (hi : i < num.val.length), IsDigitOrQuestion (num.val.get ⟨i, hi⟩)) :
    ∃ r : Bool,
      Aegis.SumGame.sum_game num = ok r ∧
        (r = true ↔
          2 * (sumLeft num.val - sumRight num.val) ≠ 9 * (qRight num.val - qLeft num.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Slice U8)
    (heven : num.val.length % 2 = 0)
    (hlower : 2 ≤ num.val.length)
    (hupper : num.val.length ≤ 100000)
    (hbytes : ∀ (i : Nat) (hi : i < num.val.length), IsDigitOrQuestion (num.val.get ⟨i, hi⟩)), ∃ r : Bool,
      Aegis.SumGame.sum_game num = ok r ∧
        (r = true ↔
          2 * (sumLeft num.val - sumRight num.val) ≠ 9 * (qRight num.val - qLeft num.val))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it never fails (no overflow, out-of-bounds access, or panic).
  Preconditions: len(num) is even, 2 <= len(num) <= 100000, and for every i with 0 <= i < len(num), num[i] is either an ASCII digit byte (48 <= num[i] <= 57) or the ASCII byte for '?' (num[i] = 63). -/
theorem spec_2 (num : Slice U8)
    (heven : num.val.length % 2 = 0)
    (hlower : 2 ≤ num.val.length)
    (hupper : num.val.length ≤ 100000)
    (hbytes : ∀ (i : Nat) (hi : i < num.val.length), IsDigitOrQuestion (num.val.get ⟨i, hi⟩)) :
    ∃ r : Bool, Aegis.SumGame.sum_game num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Slice U8)
    (heven : num.val.length % 2 = 0)
    (hlower : 2 ≤ num.val.length)
    (hupper : num.val.length ≤ 100000)
    (hbytes : ∀ (i : Nat) (hi : i < num.val.length), IsDigitOrQuestion (num.val.get ⟨i, hi⟩)), ∃ r : Bool, Aegis.SumGame.sum_game num = ok r) := by
  sorry

end AegisSpec.SumGame
