import Aegis.GetKth.Code.Funs

/-!
# Specifications of `Aegis.GetKth.get_kth`

LeetCode problem `sort-integers-by-the-power-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Classical

  namespace AegisSpec.GetKth

  def collatzStep (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else 3 * x + 1

  def collatzIter : ℕ → ℤ → ℤ
    | 0, x => x
    | n + 1, x => collatzIter n (collatzStep x)

  noncomputable def collatzPower (x : ℤ) : ℕ :=
    if h : ∃ n : ℕ, collatzIter n x = 1 then Nat.find h else 0

  lemma collatzPower_eq_find (x : ℤ) (h : ∃ n : ℕ, collatzIter n x = 1) :
      collatzPower x = Nat.find h := by
    unfold collatzPower
    exact dite_eq_left h

  lemma collatzIter_collatzPower (x : ℤ) (h : ∃ n : ℕ, collatzIter n x = 1) :
      collatzIter (collatzPower x) x = 1 := by
    rw [collatzPower_eq_find x h]
    exact Nat.find_spec h

  def lexLt (a b : ℕ × ℤ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

  def lexLe (a b : ℕ × ℤ) : Prop := lexLt a b ∨ a = b

  def rangeVals (lo hi : ℤ) : List ℤ :=
    (List.range (hi - lo + 1).toNat).map (fun i => lo + (i : ℤ))

  noncomputable def sortedVals (lo hi : ℤ) : List ℤ :=
    (rangeVals lo hi).mergeSort
      (fun a b => decide (lexLe (collatzPower a, a) (collatzPower b, b)))

  noncomputable def countLexLt (lo hi : ℤ) (p : ℕ × ℤ) : ℤ :=
    ((rangeVals lo hi).countP (fun x => decide (lexLt (collatzPower x, x) p)) : ℤ)

  noncomputable def countLexGt (lo hi : ℤ) (p : ℕ × ℤ) : ℤ :=
    ((rangeVals lo hi).countP (fun x => decide (lexLt p (collatzPower x, x))) : ℤ)

  noncomputable def countPowerLt (lo hi : ℤ) (n : ℕ) : ℤ :=
    ((rangeVals lo hi).countP (fun x => decide (collatzPower x < n)) : ℤ)

  noncomputable def countPowerLe (lo hi : ℤ) (n : ℕ) : ℤ :=
    ((rangeVals lo hi).countP (fun x => decide (collatzPower x ≤ n)) : ℤ)

  noncomputable def countPowerEqLt (lo hi : ℤ) (n : ℕ) (r : ℤ) : ℤ :=
    ((rangeVals lo hi).countP (fun x => decide (collatzPower x = n ∧ x < r)) : ℤ)

  /-- Define f(x) = x/2 when x is even and f(x) = 3*x + 1 when x is odd, for integers x >= 1. Define P(x) as the least n >= 0 such that applying f n times to x equals 1. Let L be the list [lo, lo+1, ..., hi] sorted in ascending lexicographic order of the key (P(x), x); that is, first by P(x), and among equal powers by x. Whenever get_kth lo hi k returns a result r, r = L[k-1], where L is 0-indexed and k is the given 1-based rank.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that for every integer x with lo <= x <= hi the Collatz iteration defined in the statement reaches 1 and P(x) fits in a 32-bit signed integer. -/
  theorem spec_1 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1)
      (hfit : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → collatzPower x ≤ 2 ^ 31 - 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        (sortedVals lo.val hi.val)[(k.val - 1).toNat]? = some r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1)
        (hfit : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → collatzPower x ≤ 2 ^ 31 - 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          (sortedVals lo.val hi.val)[(k.val - 1).toNat]? = some r.val) := by
    sorry

  /-- The function get_kth lo hi k returns a result r; it does not fail by panic, out-of-bounds indexing, or signed 64-bit arithmetic overflow.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that for every integer x with lo <= x <= hi the Collatz iteration reaches 1 and P(x) fits in a 32-bit signed integer. -/
  theorem spec_2 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1)
      (hfit : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → collatzPower x ≤ 2 ^ 31 - 1) :
      ∃ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1)
        (hfit : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → collatzPower x ≤ 2 ^ 31 - 1), ∃ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r) := by
    sorry

  /-- Whenever get_kth lo hi k returns a result r, lo <= r <= hi.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. -/
  theorem spec_3 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val) := by
    sorry

  /-- Define P(x) as in spec_1: the number of Collatz steps from x to 1. Whenever get_kth lo hi k returns a result r, r lies in [lo, hi] and the number of integers x with lo <= x <= hi and (P(x), x) < (P(r), r) in lexicographic order is exactly k-1.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_4 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          countLexLt lo.val hi.val (collatzPower r.val, r.val) = k.val - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            countLexLt lo.val hi.val (collatzPower r.val, r.val) = k.val - 1) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi k returns a result r, r lies in [lo, hi] and the number of integers x with lo <= x <= hi and (P(r), r) < (P(x), x) in lexicographic order is exactly hi - lo + 1 - k.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_5 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          countLexGt lo.val hi.val (collatzPower r.val, r.val)
            = hi.val - lo.val + 1 - k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            countLexGt lo.val hi.val (collatzPower r.val, r.val)
              = hi.val - lo.val + 1 - k.val) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi k returns a result r, r lies in [lo, hi] and the number of integers x with lo <= x <= hi and P(x) < P(r) is strictly less than k.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_6 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          countPowerLt lo.val hi.val (collatzPower r.val) < k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            countPowerLt lo.val hi.val (collatzPower r.val) < k.val) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi k returns a result r, r lies in [lo, hi] and the number of integers x with lo <= x <= hi and P(x) <= P(r) is at least k.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_7 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          k.val ≤ countPowerLe lo.val hi.val (collatzPower r.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            k.val ≤ countPowerLe lo.val hi.val (collatzPower r.val)) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi k returns a result r, r lies in [lo, hi]. Let C be the number of integers x with lo <= x <= hi and P(x) < P(r). Then the number of integers x with lo <= x <= hi, P(x) = P(r), and x < r is exactly k - 1 - C.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_8 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          countPowerEqLt lo.val hi.val (collatzPower r.val) r.val
            = k.val - 1 - countPowerLt lo.val hi.val (collatzPower r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            countPowerEqLt lo.val hi.val (collatzPower r.val) r.val
              = k.val - 1 - countPowerLt lo.val hi.val (collatzPower r.val)) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. If get_kth lo hi k1 returns r1 and get_kth lo hi k2 returns r2, then (P(r1), r1) < (P(r2), r2) in lexicographic order.
    Preconditions: lo, hi, k1 and k2 are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k1 < k2 <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_9 (lo hi k1 k2 : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k1.val) (hkk : k1.val < k2.val) (hk2 : k2.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r1 r2 : Std.I64, Aegis.GetKth.get_kth lo hi k1 = ok r1 →
        Aegis.GetKth.get_kth lo hi k2 = ok r2 →
          lexLt (collatzPower r1.val, r1.val) (collatzPower r2.val, r2.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (lo hi k1 k2 : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k1.val) (hkk : k1.val < k2.val) (hk2 : k2.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r1 r2 : Std.I64, Aegis.GetKth.get_kth lo hi k1 = ok r1 →
          Aegis.GetKth.get_kth lo hi k2 = ok r2 →
            lexLt (collatzPower r1.val, r1.val) (collatzPower r2.val, r2.val)) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi 1 returns a result r, r lies in [lo, hi], and for every integer x with lo <= x <= hi, (P(r), r) <= (P(x), x) in lexicographic order. Equivalently, P(r) is minimal on [lo, hi] and r is the smallest integer attaining that minimal power.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000, k = 1, and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_10 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk0 : k.val = 1) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val →
            lexLe (collatzPower r.val, r.val) (collatzPower x, x) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk0 : k.val = 1) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val →
              lexLe (collatzPower r.val, r.val) (collatzPower x, x)) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi (hi - lo + 1) returns a result r, r lies in [lo, hi], and for every integer x with lo <= x <= hi, (P(x), x) <= (P(r), r) in lexicographic order. Equivalently, P(r) is maximal on [lo, hi] and r is the largest integer attaining that maximal power.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000, k = hi - lo + 1, and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_11 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk0 : k.val = hi.val - lo.val + 1) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val →
            lexLe (collatzPower x, x) (collatzPower r.val, r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk0 : k.val = hi.val - lo.val + 1) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val →
              lexLe (collatzPower x, x) (collatzPower r.val, r.val)) := by
    sorry

  /-- Whenever get_kth lo hi k returns a result r, r = lo = hi.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000, lo = hi, and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) is defined for every x in [lo, hi]. -/
  theorem spec_12 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (heq : lo.val = hi.val)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        r.val = lo.val ∧ r.val = hi.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (heq : lo.val = hi.val)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          r.val = lo.val ∧ r.val = hi.val) := by
    sorry

  /-- Define P(x) as the number of Collatz steps from x to 1. Whenever get_kth lo hi k returns a result r, r lies in [lo, hi] and 0 <= P(r) <= 2^31 - 1.
    Preconditions: lo, hi and k are mathematical integers represented by Std.I64, with 1 <= lo <= hi <= 1000 and 1 <= k <= hi - lo + 1. The problem guarantees that P(x) fits in a 32-bit signed integer for every x in [lo, hi]. -/
  theorem spec_13 (lo hi k : Std.I64)
      (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
      (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1)
      (hfit : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → collatzPower x ≤ 2 ^ 31 - 1) :
      ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
        lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
          0 ≤ (collatzPower r.val : ℤ) ∧ (collatzPower r.val : ℤ) ≤ 2 ^ 31 - 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (lo hi k : Std.I64)
        (hlo : 1 ≤ lo.val) (hle : lo.val ≤ hi.val) (hhi : hi.val ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ hi.val - lo.val + 1)
        (hterm : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → ∃ n : ℕ, collatzIter n x = 1)
        (hfit : ∀ x : ℤ, lo.val ≤ x → x ≤ hi.val → collatzPower x ≤ 2 ^ 31 - 1), ∀ r : Std.I64, Aegis.GetKth.get_kth lo hi k = ok r →
          lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
            0 ≤ (collatzPower r.val : ℤ) ∧ (collatzPower r.val : ℤ) ≤ 2 ^ 31 - 1) := by
    sorry

  end AegisSpec.GetKth
