import Aegis.MakeStringsEqual.Code.Funs

/-!
# Specifications of `Aegis.MakeStringsEqual.make_strings_equal`

LeetCode problem `apply-bitwise-operations-to-make-strings-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MakeStringsEqual

namespace AegisSpec.MakeStringsEqual

def byteValAt (l : List Std.U8) (i : Nat) : Option Nat := (l[i]?).map (fun b => b.val)

def atOne (l : List Std.U8) (i : Nat) : Prop := byteValAt l i = some 49

def atZero (l : List Std.U8) (i : Nat) : Prop := byteValAt l i = some 48

def hasOneList (l : List Std.U8) : Prop := ∃ i : Nat, i < l.length ∧ atOne l i

def isBinaryList (l : List Std.U8) : Prop := ∀ b ∈ l, b.val = 48 ∨ b.val = 49

def isAllZeroList (l : List Std.U8) : Prop := ∀ b ∈ l, b.val = 48

def stepChain (u v : List Std.U8) : Prop :=
  ∃ i j : Nat, i < u.length ∧ j < u.length ∧ i ≠ j ∧ v.length = u.length ∧
    (atOne v i ↔ (atOne u i ∨ atOne u j)) ∧
    (atOne v j ↔ Xor (atOne u i) (atOne u j)) ∧
    (∀ m : Nat, m < u.length → m ≠ i → m ≠ j → byteValAt v m = byteValAt u m)

def reachable (s target : Slice Std.U8) : Prop :=
  ∃ (k : Nat) (u : Nat → List Std.U8),
    u 0 = s.val ∧ u k = target.val ∧
    (∀ t : Nat, t ≤ k → (u t).length = s.val.length ∧ isBinaryList (u t)) ∧
    (∀ t : Nat, t < k → stepChain (u t) (u (t + 1)))

/-- make_strings_equal returns a result r and does not fail. The Boolean r is true if and only if the following two propositions have the same truth value: (A) there exists an index i with 0 <= i < n such that s[i] = 49; (B) there exists an index j with 0 <= j < n such that target[j] = 49. Equivalently, r is true exactly when either both s and target contain at least one '1', or both consist entirely of '0's.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and for every i with 0 <= i < n, s[i] is either 48 (ASCII '0') or 49 (ASCII '1'), and target[i] is either 48 or 49. -/
theorem spec_1
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val) :
    ∃ r : Bool, make_strings_equal s target = ok r ∧
      (r = true ↔ (hasOneList s.val ↔ hasOneList target.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val), ∃ r : Bool, make_strings_equal s target = ok r ∧
      (r = true ↔ (hasOneList s.val ↔ hasOneList target.val))) := by
  sorry

/-- For every pair of inputs satisfying the preconditions, make_strings_equal returns some Boolean value r; it does not fail, panic, overflow, or access an index outside 0 <= i < n.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and all entries of s and target are either 48 or 49. -/
theorem spec_2
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val) :
    ∃ r : Bool, make_strings_equal s target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val), ∃ r : Bool, make_strings_equal s target = ok r) := by
  sorry

/-- Let r1 be the Boolean returned for inputs (s, target), and let r2 be the Boolean returned for inputs (target, s), where the two arguments are swapped. Then r1 = r2.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and all entries of s and target are either 48 or 49. -/
theorem spec_3
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val) :
    ∃ r1 r2 : Bool,
      make_strings_equal s target = ok r1 ∧ make_strings_equal target s = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val), ∃ r1 r2 : Bool,
      make_strings_equal s target = ok r1 ∧ make_strings_equal target s = ok r2 ∧ r1 = r2) := by
  sorry

/-- For every m with 2 <= m <= 100000 and every binary slices s2 and target2 of length m, if the statement 'there exists i with 0 <= i < m and s2[i] = 49' has the same truth value as 'there exists i with 0 <= i < n and s[i] = 49', and likewise 'there exists j with 0 <= j < m and target2[j] = 49' has the same truth value as 'there exists j with 0 <= j < n and target[j] = 49', then make_strings_equal s2 target2 returns the same Boolean value as make_strings_equal s target.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and all entries of s and target are either 48 or 49. -/
theorem spec_4
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val)
    (m : Nat) (s2 target2 : Slice Std.U8)
    (hms : m = s2.val.length) (hmt : m = target2.val.length)
    (hmlo : 2 ≤ m) (hmhi : m ≤ 100000)
    (hs2 : isBinaryList s2.val) (ht2 : isBinaryList target2.val)
    (hone_s : hasOneList s2.val ↔ hasOneList s.val)
    (hone_t : hasOneList target2.val ↔ hasOneList target.val) :
    ∃ r : Bool, make_strings_equal s2 target2 = ok r ∧ make_strings_equal s target = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val)
    (m : Nat) (s2 target2 : Slice Std.U8)
    (hms : m = s2.val.length) (hmt : m = target2.val.length)
    (hmlo : 2 ≤ m) (hmhi : m ≤ 100000)
    (hs2 : isBinaryList s2.val) (ht2 : isBinaryList target2.val)
    (hone_s : hasOneList s2.val ↔ hasOneList s.val)
    (hone_t : hasOneList target2.val ↔ hasOneList target.val), ∃ r : Bool, make_strings_equal s2 target2 = ok r ∧ make_strings_equal s target = ok r) := by
  sorry

/-- Whenever make_strings_equal returns true for s and target, there exist k >= 0 and byte arrays u_0, u_1, ..., u_k of length n, each entry being 48 or 49, such that u_0 = s, u_k = target, and for every t with 0 <= t < k there are distinct indices i and j with 0 <= i,j < n for which: (a) u_{t+1}[i] = 49 if and only if u_t[i] = 49 or u_t[j] = 49; (b) u_{t+1}[j] = 49 if and only if exactly one of u_t[i] and u_t[j] equals 49; and (c) u_{t+1}[m] = u_t[m] for every m with 0 <= m < n and m not in {i,j}.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and all entries of s and target are either 48 or 49. -/
theorem spec_5
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val) :
    make_strings_equal s target = ok true → reachable s target := by
  sorry

theorem spec_5_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val), make_strings_equal s target = ok true → reachable s target) := by
  sorry

/-- Whenever make_strings_equal returns false for s and target, there do not exist k >= 0 and byte arrays u_0, u_1, ..., u_k of length n, each entry being 48 or 49, such that u_0 = s, u_k = target, and for every t with 0 <= t < k there are distinct indices i and j with 0 <= i,j < n for which: (a) u_{t+1}[i] = 49 if and only if u_t[i] = 49 or u_t[j] = 49; (b) u_{t+1}[j] = 49 if and only if exactly one of u_t[i] and u_t[j] equals 49; and (c) u_{t+1}[m] = u_t[m] for every m with 0 <= m < n and m not in {i,j}.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and all entries of s and target are either 48 or 49. -/
theorem spec_6
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val) :
    make_strings_equal s target = ok false → ¬ reachable s target := by
  sorry

theorem spec_6_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val), make_strings_equal s target = ok false → ¬ reachable s target) := by
  sorry

/-- If make_strings_equal returns false, then exactly one of the following two cases holds: (1) every entry of s is 48 and there exists j with 0 <= j < n such that target[j] = 49; or (2) every entry of target is 48 and there exists i with 0 <= i < n such that s[i] = 49.
  Preconditions: Let n = len(s). The inputs satisfy n = len(target), 2 <= n <= 100000, and all entries of s and target are either 48 or 49. -/
theorem spec_7
    {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val) :
    make_strings_equal s target = ok false →
      Xor (isAllZeroList s.val ∧ hasOneList target.val)
        (isAllZeroList target.val ∧ hasOneList s.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ {n : Nat} (s target : Slice Std.U8)
    (hns : n = s.val.length) (hnt : n = target.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hs : isBinaryList s.val) (ht : isBinaryList target.val), make_strings_equal s target = ok false →
      Xor (isAllZeroList s.val ∧ hasOneList target.val)
        (isAllZeroList target.val ∧ hasOneList s.val)) := by
  sorry

end AegisSpec.MakeStringsEqual
