import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `number-of-ways-to-reach-a-position-after-exactly-k-steps`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfWays

open Aegis.NumberOfWays (number_of_ways)

def MOD : ℤ := 1000000007

def binomCount (k d : ℤ) : ℤ :=
  if (k + d) % 2 = 0 ∧ 0 ≤ (k + d) / 2 ∧ (k + d) / 2 ≤ k then
    (Nat.choose k.toNat ((k + d) / 2).toNat : ℤ)
  else 0

def canonicalWays (k d : ℤ) : ℤ := binomCount k d % MOD

/-- Let MOD = 1000000007 and d = endPos - startPos. If k + d is odd, or if m = (k + d)/2 is not an integer with 0 <= m <= k, let c = 0. Otherwise let c = C(k, m), the binomial coefficient counting the number of ways to choose m of the k steps to be rightward moves. The function returns a result r such that 0 <= r < MOD and r is the canonical residue of c modulo MOD, equivalently r ≡ c (mod MOD).
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_1 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64,
      number_of_ways startPos endPos k = ok r ∧
        0 ≤ r.val ∧ r.val < MOD ∧
          Int.ModEq MOD r.val (binomCount k.val (endPos.val - startPos.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
      number_of_ways startPos endPos k = ok r ∧
        0 ≤ r.val ∧ r.val < MOD ∧
          Int.ModEq MOD r.val (binomCount k.val (endPos.val - startPos.val))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, go out of bounds, or panic.
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_2 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64, number_of_ways startPos endPos k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64, number_of_ways startPos endPos k = ok r) := by
  sorry

/-- For every input satisfying the preconditions, the returned result r satisfies 0 <= r < 1000000007.
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_3 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000) :
    ∀ r : Std.I64, number_of_ways startPos endPos k = ok r → 0 ≤ r.val ∧ r.val < MOD := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000), ∀ r : Std.I64, number_of_ways startPos endPos k = ok r → 0 ≤ r.val ∧ r.val < MOD) := by
  sorry

/-- For every input satisfying the preconditions, if k + endPos - startPos is odd, then the function returns 0.
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_4 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hodd : Odd (k.val + endPos.val - startPos.val)) :
    number_of_ways startPos endPos k = ok 0#i64 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hodd : Odd (k.val + endPos.val - startPos.val)), number_of_ways startPos endPos k = ok 0#i64) := by
  sorry

/-- For every input satisfying the preconditions, if |endPos - startPos| > k, then the function returns 0.
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_5 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hfar : k.val < |endPos.val - startPos.val|) :
    number_of_ways startPos endPos k = ok 0#i64 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hfar : k.val < |endPos.val - startPos.val|), number_of_ways startPos endPos k = ok 0#i64) := by
  sorry

/-- For every input satisfying the preconditions, if |endPos - startPos| = k, then the function returns 1.
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_6 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hwalk : |endPos.val - startPos.val| = k.val) :
    number_of_ways startPos endPos k = ok 1#i64 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hwalk : |endPos.val - startPos.val| = k.val), number_of_ways startPos endPos k = ok 1#i64) := by
  sorry

/-- For every input satisfying the preconditions, the value returned for (startPos, endPos, k) equals the value returned for (endPos, startPos, k).
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000. -/
theorem spec_7 (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000) :
    ∃ r : Std.I64, number_of_ways startPos endPos k = ok r ∧ number_of_ways endPos startPos k = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (startPos endPos k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64, number_of_ways startPos endPos k = ok r ∧ number_of_ways endPos startPos k = ok r) := by
  sorry

/-- For any two inputs (startPos, endPos, k) and (startPos', endPos', k) satisfying the preconditions, if endPos - startPos = endPos' - startPos', then the value returned for (startPos, endPos, k) equals the value returned for (startPos', endPos', k).
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000, and the same bounds hold for every auxiliary start/end pair mentioned in the statement. -/
theorem spec_8 (startPos endPos startPos' endPos' k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hstartPos' : 0 ≤ startPos'.val ∧ startPos'.val ≤ 1000)
    (hendPos' : 0 ≤ endPos'.val ∧ endPos'.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hshift : endPos.val - startPos.val = endPos'.val - startPos'.val) :
    ∃ r : Std.I64,
      number_of_ways startPos endPos k = ok r ∧ number_of_ways startPos' endPos' k = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (startPos endPos startPos' endPos' k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hstartPos' : 0 ≤ startPos'.val ∧ startPos'.val ≤ 1000)
    (hendPos' : 0 ≤ endPos'.val ∧ endPos'.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hshift : endPos.val - startPos.val = endPos'.val - startPos'.val), ∃ r : Std.I64,
      number_of_ways startPos endPos k = ok r ∧ number_of_ways startPos' endPos' k = ok r) := by
  sorry

/-- For every input satisfying the preconditions, the value returned for (startPos, endPos, k) equals the value returned for (startPos, 2*startPos - endPos, k).
  Preconditions: 0 <= startPos <= 1000, 0 <= endPos <= 1000, 0 <= k <= 1000, and 0 <= 2*startPos - endPos <= 1000. -/
theorem spec_9 (startPos endPos endPos' k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hreflect_bounds : 0 ≤ 2 * startPos.val - endPos.val ∧ 2 * startPos.val - endPos.val ≤ 1000)
    (hendPos' : endPos'.val = 2 * startPos.val - endPos.val) :
    ∃ r : Std.I64,
      number_of_ways startPos endPos k = ok r ∧ number_of_ways startPos endPos' k = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (startPos endPos endPos' k : Std.I64)
    (hstartPos : 0 ≤ startPos.val ∧ startPos.val ≤ 1000)
    (hendPos : 0 ≤ endPos.val ∧ endPos.val ≤ 1000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000)
    (hreflect_bounds : 0 ≤ 2 * startPos.val - endPos.val ∧ 2 * startPos.val - endPos.val ≤ 1000)
    (hendPos' : endPos'.val = 2 * startPos.val - endPos.val), ∃ r : Std.I64,
      number_of_ways startPos endPos k = ok r ∧ number_of_ways startPos endPos' k = ok r) := by
  sorry

end AegisSpec.NumberOfWays
