import Aegis.CanBeValid.Code.Funs

/-!
# Specifications of `Aegis.CanBeValid.can_be_valid`

LeetCode problem `check-if-a-parentheses-string-can-be-valid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CanBeValid

  namespace AegisSpec.CanBeValid

  def cLParen : Nat := 40

  def cRParen : Nat := 41

  def cZero : Nat := 48

  def cOne : Nat := 49

  def IsLParen (c : Std.U8) : Prop := c.val = cLParen

  def IsRParen (c : Std.U8) : Prop := c.val = cRParen

  def IsParen (c : Std.U8) : Prop := IsLParen c ∨ IsRParen c

  def len (s : Slice Std.U8) : Nat := s.val.length

  def byteAt (l : List Std.U8) (i : Nat) : Option Nat := (l[i]?).map fun c => c.val

  def sliceAt (s : Slice Std.U8) (i : Nat) : Option Nat := byteAt s.val i

  def countUpTo (l : List Std.U8) (b : Nat) (k : Nat) : Nat :=
    (l.take k).countP fun c => c.val == b

  def openUpTo (l : List Std.U8) (k : Nat) : Nat := countUpTo l cLParen k

  def closeUpTo (l : List Std.U8) (k : Nat) : Nat := countUpTo l cRParen k

  def IsBalanced (l : List Std.U8) : Prop :=
    (∀ k, k ≤ l.length → closeUpTo l k ≤ openUpTo l k) ∧
      openUpTo l l.length = closeUpTo l l.length

  def lockedCountUpTo (s locked : Slice Std.U8) (b : Nat) (k : Nat) : Nat :=
    ((s.val.zip locked.val).take k).countP fun p => p.2.val == cOne && p.1.val == b

  def lockedCountFrom (s locked : Slice Std.U8) (b : Nat) (k : Nat) : Nat :=
    ((s.val.zip locked.val).drop k).countP fun p => p.2.val == cOne && p.1.val == b

  def swapParen (c : Std.U8) : Std.U8 := if c.val == cRParen then 40#u8 else 41#u8

  def mirrorList (l : List Std.U8) : List Std.U8 := l.reverse.map swapParen

  def mirrorSlice (s : Slice Std.U8) : Slice Std.U8 :=
    Slice.from (mirrorList s.val) (by
      rw [mirrorList, List.length_map, List.length_reverse]
      rw [show s.val.length = s.leng from Aeneas.Data.ListN.ListN_length s.list]
      exact Slice.bound s)

  def reverseSlice (locked : Slice Std.U8) : Slice Std.U8 :=
    Slice.from locked.val.reverse (by
      rw [List.length_reverse]
      rw [show locked.val.length = locked.leng from Aeneas.Data.ListN.ListN_length locked.list]
      exact Slice.bound locked)

  /-- Whenever can_be_valid(s, locked) returns a result r, r = true if and only if there exists a sequence t of length len(s) such that: (1) every entry of t is '(' or ')'; (2) for every i with 0 <= i < len(s), if locked[i] = '1' then t[i] = s[i]; (3) t is a balanced parentheses string, i.e., for every k with 0 <= k <= len(s) the number of indices i with 0 <= i < k and t[i] = '(' is at least the number of indices i with 0 <= i < k and t[i] = ')', and the total number of '(' in t equals the total number of ')' in t.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_1 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r) :
      (r = true ↔
        ∃ t : List Std.U8,
          t.length = len s ∧
            (∀ c, c ∈ t → IsParen c) ∧
              (∀ i, i < len s → sliceAt locked i = some cOne → byteAt t i = sliceAt s i) ∧
                IsBalanced t) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r), (r = true ↔
          ∃ t : List Std.U8,
            t.length = len s ∧
              (∀ c, c ∈ t → IsParen c) ∧
                (∀ i, i < len s → sliceAt locked i = some cOne → byteAt t i = sliceAt s i) ∧
                  IsBalanced t)) := by
    sorry

  /-- For every s and locked satisfying the preconditions, can_be_valid(s, locked) returns a result r (it does not fail).
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_2 (s locked : Slice Std.U8)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne) :
      ∃ r : Bool, can_be_valid s locked = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s locked : Slice Std.U8)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne), ∃ r : Bool, can_be_valid s locked = ok r) := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if r = true then len(s) is even.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_3 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r) :
      r = true → Even (len s) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r), r = true → Even (len s)) := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if r = true then 2 * A <= len(s) and 2 * B <= len(s), where A is the number of indices i with 0 <= i < len(s), locked[i] = '1', and s[i] = '(', and B is the number of indices i with 0 <= i < len(s), locked[i] = '1', and s[i] = ')'.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_4 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r) :
      r = true →
        2 * lockedCountUpTo s locked cLParen (len s) ≤ len s ∧
          2 * lockedCountUpTo s locked cRParen (len s) ≤ len s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r), r = true →
          2 * lockedCountUpTo s locked cLParen (len s) ≤ len s ∧
            2 * lockedCountUpTo s locked cRParen (len s) ≤ len s) := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if s is a balanced parentheses string (for every k with 0 <= k <= len(s) the prefix s[0..k) has at least as many '(' as ')', and the total numbers of '(' and ')' in s are equal), then r = true.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_5 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r) :
      IsBalanced s.val → r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r), IsBalanced s.val → r = true) := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if locked[i] = '1' for every i with 0 <= i < len(s), then r = true if and only if s is a balanced parentheses string (for every k with 0 <= k <= len(s) the prefix s[0..k) has at least as many '(' as ')', and the total numbers of '(' and ')' in s are equal).
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_6 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r)
      (hall : ∀ i, i < len s → sliceAt locked i = some cOne) :
      (r = true ↔ IsBalanced s.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r)
        (hall : ∀ i, i < len s → sliceAt locked i = some cOne), (r = true ↔ IsBalanced s.val)) := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if locked[i] = '0' for every i with 0 <= i < len(s), then r = true if and only if len(s) is even.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_7 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r)
      (hnone : ∀ i, i < len s → sliceAt locked i = some cZero) :
      (r = true ↔ Even (len s)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r)
        (hnone : ∀ i, i < len s → sliceAt locked i = some cZero), (r = true ↔ Even (len s))) := by
    sorry

  /-- For any s1, s2, and locked of common length satisfying the preconditions, if s1[i] = s2[i] for every i with 0 <= i < len(locked) and locked[i] = '1', then for any results r1 and r2 returned by can_be_valid(s1, locked) and can_be_valid(s2, locked) respectively, r1 = r2.
    Preconditions: len(s1) = len(s2) = len(locked); len(locked) >= 1; for every i with 0 <= i < len(locked), s1[i] and s2[i] are '(' or ')', and locked[i] is '0' or '1'. -/
  theorem spec_8 (s1 s2 locked : Slice Std.U8) (r1 r2 : Bool)
      (h1 : len s1 = len locked)
      (h2 : len s2 = len locked)
      (hne : 1 ≤ len locked)
      (hs1 : ∀ i, i < len locked →
        sliceAt s1 i = some cLParen ∨ sliceAt s1 i = some cRParen)
      (hs2 : ∀ i, i < len locked →
        sliceAt s2 i = some cLParen ∨ sliceAt s2 i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hagree : ∀ i, i < len locked →
        sliceAt locked i = some cOne → sliceAt s1 i = sliceAt s2 i)
      (hr1 : can_be_valid s1 locked = ok r1)
      (hr2 : can_be_valid s2 locked = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s1 s2 locked : Slice Std.U8) (r1 r2 : Bool)
        (h1 : len s1 = len locked)
        (h2 : len s2 = len locked)
        (hne : 1 ≤ len locked)
        (hs1 : ∀ i, i < len locked →
          sliceAt s1 i = some cLParen ∨ sliceAt s1 i = some cRParen)
        (hs2 : ∀ i, i < len locked →
          sliceAt s2 i = some cLParen ∨ sliceAt s2 i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hagree : ∀ i, i < len locked →
          sliceAt locked i = some cOne → sliceAt s1 i = sliceAt s2 i)
        (hr1 : can_be_valid s1 locked = ok r1)
        (hr2 : can_be_valid s2 locked = ok r2), r1 = r2) := by
    sorry

  /-- Let n = len(s). Define sequences s' and locked' of length n by s'[i] = '(' if s[n-1-i] = ')' and s'[i] = ')' otherwise, and locked'[i] = locked[n-1-i], for every i with 0 <= i < n. Then for any result r returned by can_be_valid(s, locked) and any result r' returned by can_be_valid(s', locked'), we have r = r'.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_9 (s locked : Slice Std.U8) (r r' : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r)
      (hr' : can_be_valid (mirrorSlice s) (reverseSlice locked) = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r r' : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r)
        (hr' : can_be_valid (mirrorSlice s) (reverseSlice locked) = ok r'), r = r') := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if r = true then for every k with 0 <= k <= len(s), 2 * C(k) <= k, where C(k) is the number of indices i with 0 <= i < k, locked[i] = '1', and s[i] = ')'.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_10 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r) :
      r = true →
        ∀ k, k ≤ len s → 2 * lockedCountUpTo s locked cRParen k ≤ k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r), r = true →
          ∀ k, k ≤ len s → 2 * lockedCountUpTo s locked cRParen k ≤ k) := by
    sorry

  /-- Whenever can_be_valid(s, locked) returns a result r, if r = true then for every k with 0 <= k <= len(s), 2 * D(k) <= len(s) - k, where D(k) is the number of indices i with k <= i < len(s), locked[i] = '1', and s[i] = '('.
    Preconditions: len(s) = len(locked); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), locked[i] is '0' or '1'. -/
  theorem spec_11 (s locked : Slice Std.U8) (r : Bool)
      (hlen : len s = len locked)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hlocked : ∀ i, i < len locked →
        sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
      (hr : can_be_valid s locked = ok r) :
      r = true →
        ∀ k, k ≤ len s → 2 * lockedCountFrom s locked cLParen k ≤ len s - k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s locked : Slice Std.U8) (r : Bool)
        (hlen : len s = len locked)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hlocked : ∀ i, i < len locked →
          sliceAt locked i = some cZero ∨ sliceAt locked i = some cOne)
        (hr : can_be_valid s locked = ok r), r = true →
          ∀ k, k ≤ len s → 2 * lockedCountFrom s locked cLParen k ≤ len s - k) := by
    sorry

  /-- Let s, lockedA, lockedB satisfy the preconditions with len(s) = len(lockedA) = len(lockedB). If for every i with 0 <= i < len(s), lockedB[i] = '1' implies lockedA[i] = '1', then for any result rA returned by can_be_valid(s, lockedA) and any result rB returned by can_be_valid(s, lockedB), if rA = true then rB = true.
    Preconditions: len(s) = len(lockedA) = len(lockedB); len(s) >= 1; for every i with 0 <= i < len(s), s[i] is '(' or ')'; for every i with 0 <= i < len(s), lockedA[i] and lockedB[i] are '0' or '1'. -/
  theorem spec_12 (s lockedA lockedB : Slice Std.U8) (rA rB : Bool)
      (h1 : len s = len lockedA)
      (h2 : len s = len lockedB)
      (hne : 1 ≤ len s)
      (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
      (hA : ∀ i, i < len s →
        sliceAt lockedA i = some cZero ∨ sliceAt lockedA i = some cOne)
      (hB : ∀ i, i < len s →
        sliceAt lockedB i = some cZero ∨ sliceAt lockedB i = some cOne)
      (hmono : ∀ i, i < len s →
        sliceAt lockedB i = some cOne → sliceAt lockedA i = some cOne)
      (hrA : can_be_valid s lockedA = ok rA)
      (hrB : can_be_valid s lockedB = ok rB) :
      rA = true → rB = true := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s lockedA lockedB : Slice Std.U8) (rA rB : Bool)
        (h1 : len s = len lockedA)
        (h2 : len s = len lockedB)
        (hne : 1 ≤ len s)
        (hs : ∀ i, i < len s → sliceAt s i = some cLParen ∨ sliceAt s i = some cRParen)
        (hA : ∀ i, i < len s →
          sliceAt lockedA i = some cZero ∨ sliceAt lockedA i = some cOne)
        (hB : ∀ i, i < len s →
          sliceAt lockedB i = some cZero ∨ sliceAt lockedB i = some cOne)
        (hmono : ∀ i, i < len s →
          sliceAt lockedB i = some cOne → sliceAt lockedA i = some cOne)
        (hrA : can_be_valid s lockedA = ok rA)
        (hrB : can_be_valid s lockedB = ok rB), rA = true → rB = true) := by
    sorry

  end AegisSpec.CanBeValid
