import Aegis.CanReach.Code.Funs

/-!
# Specifications of `Aegis.CanReach.can_reach`

LeetCode problem `jump-game-vii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanReach

def byteAt (s : Slice U8) (i : Nat) : Option Nat := (s.val[i]?).map (fun b => b.val)

def isByte (s : Slice U8) (i : Nat) (c : Nat) : Prop := byteAt s i = some c

def isZero (s : Slice U8) (i : Nat) : Prop := isByte s i 48

def isOne (s : Slice U8) (i : Nat) : Prop := isByte s i 49

def GapsWithin (minJump maxJump : Int) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      minJump ≤ (b : Int) - (a : Int) ∧ (b : Int) - (a : Int) ≤ maxJump ∧
        GapsWithin minJump maxJump (b :: rest)

def GapsLe (maxJump : Int) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (b : Int) - (a : Int) ≤ maxJump ∧ GapsLe maxJump (b :: rest)

def IsPath (s : Slice U8) (n : Nat) (minJump maxJump : Int) (ps : List Nat) : Prop :=
  2 ≤ ps.length ∧ ps.head? = some 0 ∧ ps.getLast? = some (n - 1) ∧
    (∀ p ∈ ps, p < n ∧ isZero s p) ∧ GapsWithin minJump maxJump ps

def Reachable (s : Slice U8) (minJump maxJump : Int) : Prop :=
  ∃ ps, IsPath s s.length minJump maxJump ps

/-- Whenever the function returns a result r, r = true if and only if there exist an integer k >= 1 and indices p_0, ..., p_k such that p_0 = 0, p_k = n-1, 0 <= p_t < n and s[p_t] = 48 for every t with 0 <= t <= k, and minJump <= p_{t+1} - p_t <= maxJump for every t with 0 <= t < k. Equivalently, r = true exactly when index n-1 is reachable from index 0 by legal moves; r = false exactly when no such sequence exists.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump <= maxJump < n. Indices are 0-based. -/
theorem spec_1 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔ Reachable s minJump.val maxJump.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔ Reachable s minJump.val maxJump.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r, which is either true or false; it does not fail, panic, or overflow.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump <= maxJump < n. -/
theorem spec_2 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    ∃ r : Bool, Aegis.CanReach.can_reach s minJump maxJump = ok r ∧ (r = true ∨ r = false) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), ∃ r : Bool, Aegis.CanReach.can_reach s minJump maxJump = ok r ∧ (r = true ∨ r = false)) := by
  sorry

/-- Whenever the function returns true, s[n-1] = 48 (the byte '0').
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump <= maxJump < n. -/
theorem spec_3 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    Aegis.CanReach.can_reach s minJump maxJump = ok true → isZero s (n - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), Aegis.CanReach.can_reach s minJump maxJump = ok true → isZero s (n - 1)) := by
  sorry

/-- The function returns true.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, 1 <= minJump <= maxJump < n, s[n-1] = 48, and minJump <= n-1 <= maxJump. -/
theorem spec_4 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hlast : isZero s (n - 1))
    (hreach_lo : minJump.val ≤ (n : Int) - 1) (hreach_hi : (n : Int) - 1 ≤ maxJump.val) :
    Aegis.CanReach.can_reach s minJump maxJump = ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hlast : isZero s (n - 1))
    (hreach_lo : minJump.val ≤ (n : Int) - 1) (hreach_hi : (n : Int) - 1 ≤ maxJump.val), Aegis.CanReach.can_reach s minJump maxJump = ok true) := by
  sorry

/-- The function returns false.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, 1 <= minJump <= maxJump < n, and for every integer j with minJump <= j <= min(maxJump, n-1), s[j] = 49. -/
theorem spec_5 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hblocked : ∀ j : Nat, minJump.val ≤ (j : Int) → (j : Int) ≤ maxJump.val →
      j ≤ n - 1 → isOne s j) :
    Aegis.CanReach.can_reach s minJump maxJump = ok false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hblocked : ∀ j : Nat, minJump.val ≤ (j : Int) → (j : Int) ≤ maxJump.val →
      j ≤ n - 1 → isOne s j), Aegis.CanReach.can_reach s minJump maxJump = ok false) := by
  sorry

/-- If the call can_reach(s,a1,b1) returns true, then the call can_reach(s,a2,b2) returns true.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), and s[0] = 48. Let a1,b1,a2,b2 be integers with 1 <= a2 <= a1 <= b1 <= b2 < n. Consider the two calls can_reach(s,a1,b1) and can_reach(s,a2,b2). -/
theorem spec_6 (s : Slice U8) (a1 b1 a2 b2 : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (ha2_pos : 1 ≤ a2.val) (ha21 : a2.val ≤ a1.val) (h1b : a1.val ≤ b1.val)
    (hb12 : b1.val ≤ b2.val) (hb2_lt : b2.val < (n : Int)) :
    Aegis.CanReach.can_reach s a1 b1 = ok true →
      Aegis.CanReach.can_reach s a2 b2 = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (a1 b1 a2 b2 : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (ha2_pos : 1 ≤ a2.val) (ha21 : a2.val ≤ a1.val) (h1b : a1.val ≤ b1.val)
    (hb12 : b1.val ≤ b2.val) (hb2_lt : b2.val < (n : Int)), Aegis.CanReach.can_reach s a1 b1 = ok true →
      Aegis.CanReach.can_reach s a2 b2 = ok true) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if d divides n-1 and, for every integer k with 1 <= k <= (n-1)/d, s[k*d] = 48.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump = maxJump = d < n. -/
theorem spec_7 (s : Slice U8) (minJump maxJump : I64) (n d : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hd_pos : 1 ≤ d) (hmin : minJump.val = (d : Int)) (hmax : maxJump.val = (d : Int))
    (hd_lt : d < n) :
    ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔
        (d ∣ (n - 1) ∧ ∀ k : Nat, 1 ≤ k → k ≤ (n - 1) / d → isZero s (k * d))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n d : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hd_pos : 1 ≤ d) (hmin : minJump.val = (d : Int)) (hmax : maxJump.val = (d : Int))
    (hd_lt : d < n), ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔
        (d ∣ (n - 1) ∧ ∀ k : Nat, 1 ≤ k → k ≤ (n - 1) / d → isZero s (k * d)))) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if there exists an integer k >= 1 such that k*minJump <= N <= k*maxJump.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, 1 <= minJump <= maxJump < n, and s[i] = 48 for every i with 0 <= i < n. Let N = n-1. -/
theorem spec_8 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hall_zero : ∀ i, i < n → isZero s i) :
    ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔
        ∃ k : Nat, 1 ≤ k ∧ (k : Int) * minJump.val ≤ (n : Int) - 1 ∧
          (n : Int) - 1 ≤ (k : Int) * maxJump.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hall_zero : ∀ i, i < n → isZero s i), ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔
        ∃ k : Nat, 1 ≤ k ∧ (k : Int) * minJump.val ≤ (n : Int) - 1 ∧
          (n : Int) - 1 ≤ (k : Int) * maxJump.val)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if maxJump = n-1.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, 1 <= minJump <= maxJump < n, s[n-1] = 48, and s[i] = 49 for every i with 1 <= i <= n-2. -/
theorem spec_9 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hlast : isZero s (n - 1))
    (hmid : ∀ i : Nat, 1 ≤ i → i ≤ n - 2 → isOne s i) :
    ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔ maxJump.val = (n : Int) - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hlast : isZero s (n - 1))
    (hmid : ∀ i : Nat, 1 ≤ i → i ≤ n - 2 → isOne s i), ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔ maxJump.val = (n : Int) - 1)) := by
  sorry

/-- Whenever the function returns true, there exists an integer j such that max(0, n-1-maxJump) <= j <= n-1-minJump and s[j] = 48.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump <= maxJump < n. -/
theorem spec_10 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    Aegis.CanReach.can_reach s minJump maxJump = ok true →
      ∃ j : Nat, max 0 (n - 1 - maxJump.val.toNat) ≤ j ∧
        j ≤ n - 1 - minJump.val.toNat ∧ isZero s j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), Aegis.CanReach.can_reach s minJump maxJump = ok true →
      ∃ j : Nat, max 0 (n - 1 - maxJump.val.toNat) ≤ j ∧
        j ≤ n - 1 - minJump.val.toNat ∧ isZero s j) := by
  sorry

/-- Whenever the function returns true, there exist an integer m with 1 <= m <= n-1 and indices p_0, ..., p_m such that p_0 = 0, p_m = n-1, 0 <= p_0 < p_1 < ... < p_m < n, s[p_t] = 48 for every t with 0 <= t <= m, and minJump <= p_{t+1} - p_t <= maxJump for every t with 0 <= t < m.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump <= maxJump < n. -/
theorem spec_11 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    Aegis.CanReach.can_reach s minJump maxJump = ok true →
      ∃ (m : Nat) (ps : List Nat), 1 ≤ m ∧ m ≤ n - 1 ∧ ps.length = m + 1 ∧
        ps.head? = some 0 ∧ ps.getLast? = some (n - 1) ∧ List.Pairwise (· < ·) ps ∧
        (∀ p ∈ ps, p < n ∧ isZero s p) ∧ GapsWithin minJump.val maxJump.val ps := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), Aegis.CanReach.can_reach s minJump maxJump = ok true →
      ∃ (m : Nat) (ps : List Nat), 1 ≤ m ∧ m ≤ n - 1 ∧ ps.length = m + 1 ∧
        ps.head? = some 0 ∧ ps.getLast? = some (n - 1) ∧ List.Pairwise (· < ·) ps ∧
        (∀ p ∈ ps, p < n ∧ isZero s p) ∧ GapsWithin minJump.val maxJump.val ps) := by
  sorry

/-- If can_reach(s, minJump, maxJump) returns true, then can_reach(t, minJump, maxJump) returns true.
  Preconditions: Let n = len(s) = len(t). Assume 2 <= n <= 100000, every byte of s and t is 48 ('0') or 49 ('1'), s[0] = t[0] = 48, 1 <= minJump <= maxJump < n, and for every i with 0 <= i < n, if s[i] = 48 then t[i] = 48. -/
theorem spec_12 (s t : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (htn : n = t.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes_s : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hbytes_t : ∀ i, i < n → isZero t i ∨ isOne t i)
    (hstart_s : isZero s 0) (hstart_t : isZero t 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hmono : ∀ i, i < n → isZero s i → isZero t i) :
    Aegis.CanReach.can_reach s minJump maxJump = ok true →
      Aegis.CanReach.can_reach t minJump maxJump = ok true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (htn : n = t.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes_s : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hbytes_t : ∀ i, i < n → isZero t i ∨ isOne t i)
    (hstart_s : isZero s 0) (hstart_t : isZero t 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int))
    (hmono : ∀ i, i < n → isZero s i → isZero t i), Aegis.CanReach.can_reach s minJump maxJump = ok true →
      Aegis.CanReach.can_reach t minJump maxJump = ok true) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if s[n-1] = 48 and there exist an integer m >= 1 and indices q_0, ..., q_m such that q_0 = 0, q_m = n-1, 0 <= q_0 < q_1 < ... < q_m < n, s[q_t] = 48 for every t with 0 <= t <= m, and q_{t+1} - q_t <= maxJump for every t with 0 <= t < m.
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, minJump = 1, and 1 <= maxJump < n. -/
theorem spec_13 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hmin : minJump.val = 1) (hmax_pos : 1 ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔
        (isZero s (n - 1) ∧
          ∃ (m : Nat) (qs : List Nat), 1 ≤ m ∧ qs.length = m + 1 ∧
            qs.head? = some 0 ∧ qs.getLast? = some (n - 1) ∧
            List.Pairwise (· < ·) qs ∧ (∀ q ∈ qs, q < n ∧ isZero s q) ∧
            GapsLe maxJump.val qs)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hmin : minJump.val = 1) (hmax_pos : 1 ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), ∀ r, Aegis.CanReach.can_reach s minJump maxJump = ok r →
      (r = true ↔
        (isZero s (n - 1) ∧
          ∃ (m : Nat) (qs : List Nat), 1 ≤ m ∧ qs.length = m + 1 ∧
            qs.head? = some 0 ∧ qs.getLast? = some (n - 1) ∧
            List.Pairwise (· < ·) qs ∧ (∀ q ∈ qs, q < n ∧ isZero s q) ∧
            GapsLe maxJump.val qs))) := by
  sorry

/-- Whenever the function returns true, every witness path p_0, ..., p_k as in spec_1 satisfies ceil((n-1)/maxJump) <= k <= floor((n-1)/minJump).
  Preconditions: Let n = len(s). Assume 2 <= n <= 100000, every byte of s is 48 ('0') or 49 ('1'), s[0] = 48, and 1 <= minJump <= maxJump < n. -/
theorem spec_14 (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)) :
    Aegis.CanReach.can_reach s minJump maxJump = ok true →
      ∀ ps : List Nat, IsPath s n minJump.val maxJump.val ps →
        (n - 1 + maxJump.val.toNat - 1) / maxJump.val.toNat ≤ ps.length - 1 ∧
          ps.length - 1 ≤ (n - 1) / minJump.val.toNat := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8) (minJump maxJump : I64) (n : Nat)
    (hn : n = s.length) (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hbytes : ∀ i, i < n → isZero s i ∨ isOne s i)
    (hstart : isZero s 0)
    (hjump_pos : 1 ≤ minJump.val) (hjump_le : minJump.val ≤ maxJump.val)
    (hjump_lt : maxJump.val < (n : Int)), Aegis.CanReach.can_reach s minJump maxJump = ok true →
      ∀ ps : List Nat, IsPath s n minJump.val maxJump.val ps →
        (n - 1 + maxJump.val.toNat - 1) / maxJump.val.toNat ≤ ps.length - 1 ∧
          ps.length - 1 ≤ (n - 1) / minJump.val.toNat) := by
  sorry

end AegisSpec.CanReach
