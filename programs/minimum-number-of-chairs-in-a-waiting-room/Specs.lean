import Aegis.MinimumChairs.Code.Funs

/-!
# Specifications of `Aegis.MinimumChairs.minimum_chairs`

LeetCode problem `minimum-number-of-chairs-in-a-waiting-room`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumChairs

abbrev bytes (s : Slice Std.U8) : List Std.U8 := s.val

def countBytes (l : List Std.U8) (b : Int) : Nat :=
  (l.filter (fun c => decide (c.val = b))).length

def B (s : Slice Std.U8) (k : Nat) : Int :=
  (countBytes (s.val.take k) 69 : Int) - (countBytes (s.val.take k) 76 : Int)

def IsMaxB (s : Slice Std.U8) (r : Int) : Prop :=
  (∀ k : Nat, k ≤ s.val.length → B s k ≤ r) ∧
    ∃ k : Nat, k ≤ s.val.length ∧ B s k = r

/-- Let n = len(s), and for 0 ≤ k ≤ n let B_s(k) be the number of indices i with 0 ≤ i < k and s[i] = 69, minus the number of indices i with 0 ≤ i < k and s[i] = 76; thus B_s(0) = 0. The function returns a result r (it does not fail), and the integer value of r is max{ B_s(k) | 0 ≤ k ≤ n }.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 (the ASCII code of 'E') or s[i] = 76 (the ASCII code of 'L'). -/
theorem spec_1 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ IsMaxB s r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ IsMaxB s r.val) := by
  sorry

/-- For every such s, the function returns a result r; it does not panic, overflow, or fail due to an out-of-bounds access.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_2 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r) := by
  sorry

/-- The function returns a result r, and 0 ≤ r.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_3 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- Let m be the number of indices i with 0 ≤ i < n and s[i] = 69. The function returns a result r, and r ≤ m.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_4 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val ≤ (countBytes s.val 69 : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val ≤ (countBytes s.val 69 : Int)) := by
  sorry

/-- Let B_s(k) be the number of indices i with 0 ≤ i < k and s[i] = 69, minus the number of indices i with 0 ≤ i < k and s[i] = 76, for 0 ≤ k ≤ n. The function returns a result r, and there exists an integer k with 0 ≤ k ≤ n such that B_s(k) = r.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_5 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        ∃ k : Nat, k ≤ s.val.length ∧ B s k = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        ∃ k : Nat, k ≤ s.val.length ∧ B s k = r.val) := by
  sorry

/-- Let B_s(k) be the number of indices i with 0 ≤ i < k and s[i] = 69, minus the number of indices i with 0 ≤ i < k and s[i] = 76, for 0 ≤ k ≤ n. The function returns a result r, and for every integer k with 0 ≤ k ≤ n, B_s(k) ≤ r.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_6 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        ∀ k : Nat, k ≤ s.val.length → B s k ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        ∀ k : Nat, k ≤ s.val.length → B s k ≤ r.val) := by
  sorry

/-- Let B_s(k) be as above. The function returns a result r, and for every integer q with 0 ≤ q < r, there exists an integer k with 0 ≤ k ≤ n such that B_s(k) > q.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_7 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        ∀ q : Int, 0 ≤ q → q < r.val → ∃ k : Nat, k ≤ s.val.length ∧ B s k > q := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        ∀ q : Int, 0 ≤ q → q < r.val → ∃ k : Nat, k ≤ s.val.length ∧ B s k > q) := by
  sorry

/-- The function returns a result r, and r = n.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50, every s[i] is either 69 or 76, and in addition s[i] = 69 for every i with 0 ≤ i < n. -/
theorem spec_8 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (hE : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69) :
    ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val = (s.val.length : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (hE : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69), ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val = (s.val.length : Int)) := by
  sorry

/-- The function returns a result r, and r = 0.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50, every s[i] is either 69 or 76, and in addition s[i] = 76 for every i with 0 ≤ i < n. -/
theorem spec_9 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (hL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 76) :
    ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (hL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 76), ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r, and 1 ≤ r.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. Assume in addition that s[0] = 69. -/
theorem spec_10 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (h0 : ∀ (h : 0 < s.val.length), (s.val[0]).val = 69) :
    ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (h0 : ∀ (h : 0 < s.val.length), (s.val[0]).val = 69), ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = 1.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. Assume in addition that s[0] = 69 and, for every i with 1 ≤ i < n, s[i] = 76. -/
theorem spec_11 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (h0 : ∀ (h : 0 < s.val.length), (s.val[0]).val = 69)
    (hrest : ∀ (i : Nat) (h1 : 1 ≤ i) (h : i < s.val.length), (s.val[i]).val = 76) :
    ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76)
    (h0 : ∀ (h : 0 < s.val.length), (s.val[0]).val = 69)
    (hrest : ∀ (i : Nat) (h1 : 1 ≤ i) (h : i < s.val.length), (s.val[i]).val = 76), ∃ r : Std.I64, Aegis.MinimumChairs.minimum_chairs s = ok r ∧ r.val = 1) := by
  sorry

/-- Let B_s(k) be the number of indices i with 0 ≤ i < k and s[i] = 69, minus the number of indices i with 0 ≤ i < k and s[i] = 76, for 0 ≤ k ≤ n. The function returns a result r, and r = 0 if and only if B_s(k) ≤ 0 for every integer k with 0 ≤ k ≤ n.
  Preconditions: Let n = len(s). Assume 1 ≤ n ≤ 50 and for every i with 0 ≤ i < n, s[i] = 69 or s[i] = 76. -/
theorem spec_12 (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76) :
    ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        (r.val = 0 ↔ ∀ k : Nat, k ≤ s.val.length → B s k ≤ 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn1 : 1 ≤ s.val.length) (hn50 : s.val.length ≤ 50)
    (hEL : ∀ (i : Nat) (h : i < s.val.length), (s.val[i]).val = 69 ∨ (s.val[i]).val = 76), ∃ r : Std.I64,
      Aegis.MinimumChairs.minimum_chairs s = ok r ∧
        (r.val = 0 ↔ ∀ k : Nat, k ≤ s.val.length → B s k ≤ 0)) := by
  sorry

end AegisSpec.MinimumChairs
