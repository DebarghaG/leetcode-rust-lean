import Aegis.CheckValidString.Code.Funs

/-!
# Specifications of `Aegis.CheckValidString.check_valid_string`

LeetCode problem `valid-parenthesis-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckValidString

open Aegis.CheckValidString

def AllParenStar (s : Slice Std.U8) : Prop :=
  ∀ i, (hi : i < s.val.length) →
    (s.val[i]).val = 40 ∨ (s.val[i]).val = 41 ∨ (s.val[i]).val = 42

def AllOpenStar (s : Slice Std.U8) : Prop :=
  ∀ i, (hi : i < s.val.length) → (s.val[i]).val = 40 ∨ (s.val[i]).val = 42

def AllCloseStar (s : Slice Std.U8) : Prop :=
  ∀ i, (hi : i < s.val.length) → (s.val[i]).val = 41 ∨ (s.val[i]).val = 42

def NoStar (s : Slice Std.U8) : Prop :=
  ∀ i, (hi : i < s.val.length) → (s.val[i]).val ≠ 42

def countRange (s : Slice Std.U8) (c : Nat) (lo hi : Nat) : Nat :=
  ((s.val.drop lo).take (hi - lo)).countP (fun b => b.val = c)

def IsBalanced (t : List Nat) : Prop :=
  (∀ b, b ∈ t → b = 40 ∨ b = 41) ∧
    t.countP (fun b => b = 40) = t.countP (fun b => b = 41) ∧
      ∀ k, k ≤ t.length →
        (t.take k).countP (fun b => b = 41) ≤ (t.take k).countP (fun b => b = 40)

inductive IsExpansion : List Std.U8 → List Nat → Prop where
  | nil : IsExpansion [] []
  | keep {b : Std.U8} {bs : List Std.U8} {t : List Nat} :
      (b.val = 40 ∨ b.val = 41) → IsExpansion bs t → IsExpansion (b :: bs) (b.val :: t)
  | left {b : Std.U8} {bs : List Std.U8} {t : List Nat} :
      b.val = 42 → IsExpansion bs t → IsExpansion (b :: bs) (40 :: t)
  | right {b : Std.U8} {bs : List Std.U8} {t : List Nat} :
      b.val = 42 → IsExpansion bs t → IsExpansion (b :: bs) (41 :: t)
  | erase {b : Std.U8} {bs : List Std.U8} {t : List Nat} :
      b.val = 42 → IsExpansion bs t → IsExpansion (b :: bs) t

def sliceOfList (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Std.Usize.max then
    ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩
  else
    Slice.new Std.U8

def insertAt {α : Type} (l : List α) (j : Nat) (a : α) : List α :=
  l.take j ++ a :: l.drop j

/-- Let n = len(s). The function returns a result r and does not fail on inputs satisfying the preconditions. It holds that r = true if and only if there exists a choice, for every index i with 0 <= i < n and s[i] = '*', of one of the three values L, R, or E, such that the following string t is a balanced parentheses string: start from the sequence s[0],...,s[n-1]; for each i with s[i] = '*', replace it by '(' if the choice is L, by ')' if the choice is R, and delete it if the choice is E; for every i with s[i] != '*', keep s[i] unchanged. A string t over '(' and ')' is called a balanced parentheses string when (1) t contains the same number of '(' and ')', and (2) for every k with 0 <= k <= len(t), the number of '(' among the first k bytes of t is greater than or equal to the number of ')' among the first k bytes of t. If no such choice exists, then r = false.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∃ r, check_valid_string s = ok r ∧
      (r = true ↔ ∃ t : List Nat, IsExpansion s.val t ∧ IsBalanced t) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∃ r, check_valid_string s = ok r ∧
      (r = true ↔ ∃ t : List Nat, IsExpansion s.val t ∧ IsBalanced t)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r and does not fail: there is no arithmetic overflow, out-of-bounds indexing, panic, or other runtime failure.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∃ r, check_valid_string s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∃ r, check_valid_string s = ok r) := by
  sorry

/-- The function returns a result r, and r = true if and only if (1) the number of indices i with 0 <= i < len(s) and s[i] = '(' equals the number of indices i with 0 <= i < len(s) and s[i] = ')', and (2) for every k with 0 <= k <= len(s), the number of indices i with 0 <= i < k and s[i] = '(' is greater than or equal to the number of indices i with 0 <= i < k and s[i] = ')'.
  Preconditions: len(s) >= 1 and len(s) <= 100, for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42), and there is no i with 0 <= i < len(s) and s[i] = '*'. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s)
    (hnostar : NoStar s) :
    ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        countRange s 40 0 s.val.length = countRange s 41 0 s.val.length ∧
          ∀ k, k ≤ s.val.length →
            countRange s 41 0 k ≤ countRange s 40 0 k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s)
    (hnostar : NoStar s), ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        countRange s 40 0 s.val.length = countRange s 41 0 s.val.length ∧
          ∀ k, k ≤ s.val.length →
            countRange s 41 0 k ≤ countRange s 40 0 k)) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the number of indices i with 0 <= i < len(s) and s[i] = ')' is at most the number of indices i with 0 <= i < len(s) and s[i] = '(' plus the number of indices i with 0 <= i < len(s) and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∀ r, check_valid_string s = ok r → r = true →
      countRange s 41 0 s.val.length ≤
        countRange s 40 0 s.val.length + countRange s 42 0 s.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∀ r, check_valid_string s = ok r → r = true →
      countRange s 41 0 s.val.length ≤
        countRange s 40 0 s.val.length + countRange s 42 0 s.val.length) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the number of indices i with 0 <= i < len(s) and s[i] = '(' is at most the number of indices i with 0 <= i < len(s) and s[i] = ')' plus the number of indices i with 0 <= i < len(s) and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∀ r, check_valid_string s = ok r → r = true →
      countRange s 40 0 s.val.length ≤
        countRange s 41 0 s.val.length + countRange s 42 0 s.val.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∀ r, check_valid_string s = ok r → r = true →
      countRange s 40 0 s.val.length ≤
        countRange s 41 0 s.val.length + countRange s 42 0 s.val.length) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every k with 0 <= k <= len(s), the number of indices i with 0 <= i < k and s[i] = ')' is at most the number of indices i with 0 <= i < k and s[i] = '(' plus the number of indices i with 0 <= i < k and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∀ r, check_valid_string s = ok r → r = true →
      ∀ k, k ≤ s.val.length →
        countRange s 41 0 k ≤ countRange s 40 0 k + countRange s 42 0 k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∀ r, check_valid_string s = ok r → r = true →
      ∀ k, k ≤ s.val.length →
        countRange s 41 0 k ≤ countRange s 40 0 k + countRange s 42 0 k) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every k with 0 <= k <= len(s), the number of indices i with k <= i < len(s) and s[i] = '(' is at most the number of indices i with k <= i < len(s) and s[i] = ')' plus the number of indices i with k <= i < len(s) and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∀ r, check_valid_string s = ok r → r = true →
      ∀ k, k ≤ s.val.length →
        countRange s 40 k s.val.length ≤
          countRange s 41 k s.val.length + countRange s 42 k s.val.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∀ r, check_valid_string s = ok r → r = true →
      ∀ k, k ≤ s.val.length →
        countRange s 40 k s.val.length ≤
          countRange s 41 k s.val.length + countRange s 42 k s.val.length) := by
  sorry

/-- The function returns a result r, and r = true if and only if for every k with 0 <= k <= len(s), the number of indices i with k <= i < len(s) and s[i] = '(' is at most the number of indices i with k <= i < len(s) and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40) or '*' (42); in particular, no s[i] is ')'. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllOpenStar s) :
    ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        ∀ k, k ≤ s.val.length →
          countRange s 40 k s.val.length ≤ countRange s 42 k s.val.length) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllOpenStar s), ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        ∀ k, k ≤ s.val.length →
          countRange s 40 k s.val.length ≤ countRange s 42 k s.val.length)) := by
  sorry

/-- The function returns a result r, and r = true if and only if for every k with 0 <= k <= len(s), the number of indices i with 0 <= i < k and s[i] = ')' is at most the number of indices i with 0 <= i < k and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of ')' (41) or '*' (42); in particular, no s[i] is '('. -/
theorem spec_9 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllCloseStar s) :
    ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        ∀ k, k ≤ s.val.length →
          countRange s 41 0 k ≤ countRange s 42 0 k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllCloseStar s), ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        ∀ k, k ≤ s.val.length →
          countRange s 41 0 k ≤ countRange s 42 0 k)) := by
  sorry

/-- Let u be the byte slice of length len(s)+2 whose bytes are s[0],...,s[len(s)-1], followed by the ASCII code of '(' and then the ASCII code of ')'. Whenever the call check_valid_string(s) returns a result r with r = true, the call check_valid_string(u) returns a result r' with r' = true.
  Preconditions: len(s) >= 1 and len(s) <= 98, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_10 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 98) (hchars : AllParenStar s) :
    let u : Slice Std.U8 := sliceOfList (s.val ++ [40#u8, 41#u8])
    ∀ r, check_valid_string s = ok r → r = true →
      ∃ r', check_valid_string u = ok r' ∧ r' = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 98) (hchars : AllParenStar s), let u : Slice Std.U8 := sliceOfList (s.val ++ [40#u8, 41#u8])
    ∀ r, check_valid_string s = ok r → r = true →
      ∃ r', check_valid_string u = ok r' ∧ r' = true) := by
  sorry

/-- Let u be the byte slice of length len(s)+2 whose first two bytes are the ASCII code of '(' and then the ASCII code of ')', followed by s[0],...,s[len(s)-1]. Whenever the call check_valid_string(s) returns a result r with r = true, the call check_valid_string(u) returns a result r' with r' = true.
  Preconditions: len(s) >= 1 and len(s) <= 98, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_11 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 98) (hchars : AllParenStar s) :
    let u : Slice Std.U8 := sliceOfList ([40#u8, 41#u8] ++ s.val)
    ∀ r, check_valid_string s = ok r → r = true →
      ∃ r', check_valid_string u = ok r' ∧ r' = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 98) (hchars : AllParenStar s), let u : Slice Std.U8 := sliceOfList ([40#u8, 41#u8] ++ s.val)
    ∀ r, check_valid_string s = ok r → r = true →
      ∃ r', check_valid_string u = ok r' ∧ r' = true) := by
  sorry

/-- Let n = len(s). The function returns a result r and does not fail. It holds that r = true if and only if both of the following hold: (1) for every k with 0 <= k <= n, the number of indices i with 0 <= i < k and s[i] = ')' is at most the number of indices i with 0 <= i < k and s[i] = '(' plus the number of indices i with 0 <= i < k and s[i] = '*'; and (2) for every k with 0 <= k <= n, the number of indices i with k <= i < n and s[i] = '(' is at most the number of indices i with k <= i < n and s[i] = ')' plus the number of indices i with k <= i < n and s[i] = '*'.
  Preconditions: len(s) >= 1 and len(s) <= 100, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_12 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s) :
    ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        (∀ k, k ≤ s.val.length →
          countRange s 41 0 k ≤ countRange s 40 0 k + countRange s 42 0 k) ∧
        (∀ k, k ≤ s.val.length →
          countRange s 40 k s.val.length ≤
            countRange s 41 k s.val.length + countRange s 42 k s.val.length)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s), ∃ r, check_valid_string s = ok r ∧
      (r = true ↔
        (∀ k, k ≤ s.val.length →
          countRange s 41 0 k ≤ countRange s 40 0 k + countRange s 42 0 k) ∧
        (∀ k, k ≤ s.val.length →
          countRange s 40 k s.val.length ≤
            countRange s 41 k s.val.length + countRange s 42 k s.val.length))) := by
  sorry

/-- For every index j with 0 <= j <= len(s), let u be the byte slice of length len(s)+1 obtained by inserting the ASCII code of '*' (42) at position j: u[i] = s[i] for 0 <= i < j, u[j] = '*', and u[i] = s[i-1] for j < i <= len(s). Whenever check_valid_string(s) returns a result r with r = true, check_valid_string(u) returns a result r' with r' = true.
  Preconditions: len(s) >= 1 and len(s) <= 99, and for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42). -/
theorem spec_13 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 99) (hchars : AllParenStar s) :
    ∀ j, j ≤ s.val.length →
      let u : Slice Std.U8 := sliceOfList (insertAt s.val j 42#u8)
      ∀ r, check_valid_string s = ok r → r = true →
        ∃ r', check_valid_string u = ok r' ∧ r' = true := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 99) (hchars : AllParenStar s), ∀ j, j ≤ s.val.length →
      let u : Slice Std.U8 := sliceOfList (insertAt s.val j 42#u8)
      ∀ r, check_valid_string s = ok r → r = true →
        ∃ r', check_valid_string u = ok r' ∧ r' = true) := by
  sorry

/-- Let u be the byte slice of length len(s) obtained from s by replacing s[j] with the ASCII code of '*' (42), leaving all other bytes unchanged. Whenever check_valid_string(s) returns a result r with r = true, check_valid_string(u) returns a result r' with r' = true.
  Preconditions: len(s) >= 1 and len(s) <= 100, for every i with 0 <= i < len(s), s[i] is the ASCII code of '(' (40), ')' (41), or '*' (42), and j is an index with 0 <= j < len(s) such that s[j] is the ASCII code of '(' or ')'. -/
theorem spec_14 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s)
    (j : Nat) (hj : j < s.val.length)
    (hjchar : (s.val[j]).val = 40 ∨ (s.val[j]).val = 41) :
    let u : Slice Std.U8 := sliceOfList (s.val.set j 42#u8)
    ∀ r, check_valid_string s = ok r → r = true →
      ∃ r', check_valid_string u = ok r' ∧ r' = true := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 100) (hchars : AllParenStar s)
    (j : Nat) (hj : j < s.val.length)
    (hjchar : (s.val[j]).val = 40 ∨ (s.val[j]).val = 41), let u : Slice Std.U8 := sliceOfList (s.val.set j 42#u8)
    ∀ r, check_valid_string s = ok r → r = true →
      ∃ r', check_valid_string u = ok r' ∧ r' = true) := by
  sorry

end AegisSpec.CheckValidString
