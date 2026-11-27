import Aegis.CharacterReplacement.Code.Funs

/-!
# Specifications of `Aegis.CharacterReplacement.character_replacement`

LeetCode problem `longest-repeating-character-replacement`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CharacterReplacement (character_replacement)

namespace AegisSpec.CharacterReplacement

def IsUppercaseByte (a : Nat) : Prop := 65 ≤ a ∧ a ≤ 90

def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def slen (s : Slice Std.U8) : Nat := (bytes s).length

def byteAt (s : Slice Std.U8) (i : Nat) : Option Nat := (bytes s)[i]?

def uppercaseLetters : List Nat := (List.range 26).map (fun j => j + 65)

def cnt (l : List Nat) (c : Nat) : Nat := (l.filter (fun b => b == c)).length

def window (l : List Nat) (lo hi : Nat) : List Nat := (l.drop lo).take (hi - lo)

def cntIn (l : List Nat) (lo hi c : Nat) : Nat := cnt (window l lo hi) c

def mismatch (l : List Nat) (lo hi c : Nat) : Nat :=
  ((window l lo hi).filter (fun b => b != c)).length

def mf (l : List Nat) (lo hi : Nat) : Nat :=
  (uppercaseLetters.map (fun c => cntIn l lo hi c)).foldr max 0

def AllSame (w : List Nat) : Prop := ∀ a ∈ w, ∀ b ∈ w, a = b

def allSameB (w : List Nat) : Bool := w.all (fun a => w.all (fun b => a == b))

def intervals (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap (fun hi => (List.range (hi + 1)).map (fun lo => (lo, hi)))

def bestWindow (l : List Nat) (k : ℤ) : Nat :=
  ((intervals l.length).filter
      (fun p => ((p.2 - p.1 : Nat) : ℤ) - (mf l p.1 p.2 : ℤ) ≤ k)).map
    (fun p => p.2 - p.1) |>.foldr max 0

def bestConstant (l : List Nat) : Nat :=
  ((intervals l.length).filter (fun p => allSameB (window l p.1 p.2))).map
    (fun p => p.2 - p.1) |>.foldr max 0

def IsLetterBijection (f : Nat → Nat) : Prop :=
  (∀ c, c ∈ uppercaseLetters → f c ∈ uppercaseLetters) ∧
    (∀ d, d ∈ uppercaseLetters → ∃! c, c ∈ uppercaseLetters ∧ f c = d)

/-- The function returns a result ans and, for every interval [lo,hi) with 0 <= lo <= hi <= n, letting cnt(c,lo,hi) = |{ i | lo <= i < hi and s[i] = c }| for an uppercase English letter c and mf(lo,hi) = max over all uppercase English letters c of cnt(c,lo,hi), we have ans = max { hi-lo | 0 <= lo <= hi <= n and (hi-lo) - mf(lo,hi) <= k }. The maximum includes empty intervals, so for n=0 it is 0.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a) :
    ∃ ans : Std.I64,
      character_replacement s k = ok ans ∧ ans.val = (bestWindow (bytes s) k.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a), ∃ ans : Std.I64,
      character_replacement s k = ok ans ∧ ans.val = (bestWindow (bytes s) k.val : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result ans; it does not fail, panic, or overflow.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a) :
    ∃ ans : Std.I64, character_replacement s k = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a), ∃ ans : Std.I64, character_replacement s k = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, 0 <= ans <= len(s).
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    0 ≤ ans.val ∧ ans.val ≤ (slen s : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), 0 ≤ ans.val ∧ ans.val ≤ (slen s : ℤ)) := by
  sorry

/-- Whenever the function returns a result ans, ans >= min(len(s), k+1).
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    min (slen s : ℤ) (k.val + 1) ≤ ans.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), min (slen s : ℤ) (k.val + 1) ≤ ans.val) := by
  sorry

/-- Whenever the function returns a result ans, ans = len(s) if and only if len(s) - mf(0,len(s)) <= k, where mf(0,len(s)) is the maximum over uppercase English letters c of the number of i with 0 <= i < len(s) and s[i] = c (and mf(0,len(s)) = 0 when len(s)=0).
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    (ans.val = (slen s : ℤ) ↔
      (slen s : ℤ) - (mf (bytes s) 0 (slen s) : ℤ) ≤ k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), (ans.val = (slen s : ℤ) ↔
      (slen s : ℤ) - (mf (bytes s) 0 (slen s) : ℤ) ≤ k.val)) := by
  sorry

/-- Whenever the function returns a result ans, ans = max { hi-lo | 0 <= lo <= hi <= len(s) and s[i] = s[j] for every lo <= i < j < hi }.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, k = 0, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hk : k.val = 0) (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    ans.val = (bestConstant (bytes s) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hk : k.val = 0) (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), ans.val = (bestConstant (bytes s) : ℤ)) := by
  sorry

/-- Whenever the function returns a result ans, there exist lo, hi and an uppercase English letter c such that 0 <= lo <= hi <= len(s), hi-lo = ans, and the number of i with lo <= i < hi and s[i] != c is at most k.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_7 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    ∃ lo hi c : Nat,
      lo ≤ hi ∧ hi ≤ slen s ∧ ((hi - lo : Nat) : ℤ) = ans.val ∧
        c ∈ uppercaseLetters ∧ ((mismatch (bytes s) lo hi c : Nat) : ℤ) ≤ k.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), ∃ lo hi c : Nat,
      lo ≤ hi ∧ hi ≤ slen s ∧ ((hi - lo : Nat) : ℤ) = ans.val ∧
        c ∈ uppercaseLetters ∧ ((mismatch (bytes s) lo hi c : Nat) : ℤ) ≤ k.val) := by
  sorry

/-- Whenever the function returns a result ans, for every lo, hi and every uppercase English letter c with 0 <= lo <= hi <= len(s), if hi-lo > ans then the number of i with lo <= i < hi and s[i] != c is greater than k.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    ∀ (lo hi c : Nat), lo ≤ hi → hi ≤ slen s → c ∈ uppercaseLetters →
      ((hi - lo : Nat) : ℤ) > ans.val → ((mismatch (bytes s) lo hi c : Nat) : ℤ) > k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), ∀ (lo hi c : Nat), lo ≤ hi → hi ≤ slen s → c ∈ uppercaseLetters →
      ((hi - lo : Nat) : ℤ) > ans.val → ((mismatch (bytes s) lo hi c : Nat) : ℤ) > k.val) := by
  sorry

/-- If ans1 is the result of character_replacement(s,k1) and ans2 is the result of character_replacement(s,k2), then ans1 <= ans2.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, every byte s[i] is an uppercase English letter for 0 <= i < n, and 0 <= k1 <= k2 <= n. -/
theorem spec_9 (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hn : slen s ≤ 100000) (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ (slen s : ℤ))
    (ans1 ans2 : Std.I64)
    (h1 : character_replacement s k1 = ok ans1) (h2 : character_replacement s k2 = ok ans2) :
    ans1.val ≤ ans2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hn : slen s ≤ 100000) (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ (slen s : ℤ))
    (ans1 ans2 : Std.I64)
    (h1 : character_replacement s k1 = ok ans1) (h2 : character_replacement s k2 = ok ans2), ans1.val ≤ ans2.val) := by
  sorry

/-- If ans_s is the result of character_replacement(s,k) and ans_t is the result of character_replacement(t,k), then ans_s = ans_t.
  Preconditions: Let n = len(s) = len(t). Assume 0 <= n <= 100000, 0 <= k <= n, every byte of s and t is an uppercase English letter, and there is a bijection f from the set of uppercase English letters to itself such that t[i] = f(s[i]) for every 0 <= i < n. -/
theorem spec_10 (s t : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hlen : slen s = slen t)
    (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hup_s : ∀ a ∈ bytes s, IsUppercaseByte a)
    (hup_t : ∀ a ∈ bytes t, IsUppercaseByte a)
    (hperm : ∃ f, IsLetterBijection f ∧ ∀ i, i < slen s → byteAt t i = (byteAt s i).map f)
    (ans_s ans_t : Std.I64)
    (hs : character_replacement s k = ok ans_s) (ht : character_replacement t k = ok ans_t) :
    ans_s.val = ans_t.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hlen : slen s = slen t)
    (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hup_s : ∀ a ∈ bytes s, IsUppercaseByte a)
    (hup_t : ∀ a ∈ bytes t, IsUppercaseByte a)
    (hperm : ∃ f, IsLetterBijection f ∧ ∀ i, i < slen s → byteAt t i = (byteAt s i).map f)
    (ans_s ans_t : Std.I64)
    (hs : character_replacement s k = ok ans_s) (ht : character_replacement t k = ok ans_t), ans_s.val = ans_t.val) := by
  sorry

/-- Whenever the function returns a result ans, ans >= L, where L = max { hi-lo | 0 <= lo <= hi <= len(s) and s[i] = s[j] for every lo <= i < j < hi }.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_11 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    (bestConstant (bytes s) : ℤ) ≤ ans.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), (bestConstant (bytes s) : ℤ) ≤ ans.val) := by
  sorry

/-- If ans_s is the result of character_replacement(s,k) and ans_t is the result of character_replacement(t,k), then ans_t <= ans_s.
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, every byte s[i] is an uppercase English letter for 0 <= i < n, t is a contiguous substring of s (there exists p with 0 <= p, p + len(t) <= n, and t[i] = s[p+i] for every 0 <= i < len(t)), every byte of t is uppercase, and 0 <= k <= len(t). -/
theorem spec_12 (s t : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000)
    (hup_s : ∀ a ∈ bytes s, IsUppercaseByte a)
    (hup_t : ∀ a ∈ bytes t, IsUppercaseByte a)
    (hsub : ∃ p, p + slen t ≤ slen s ∧ ∀ i, i < slen t → byteAt t i = byteAt s (p + i))
    (hk0 : 0 ≤ k.val) (hkt : k.val ≤ (slen t : ℤ))
    (ans_s ans_t : Std.I64)
    (hs : character_replacement s k = ok ans_s) (ht : character_replacement t k = ok ans_t) :
    ans_t.val ≤ ans_s.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000)
    (hup_s : ∀ a ∈ bytes s, IsUppercaseByte a)
    (hup_t : ∀ a ∈ bytes t, IsUppercaseByte a)
    (hsub : ∃ p, p + slen t ≤ slen s ∧ ∀ i, i < slen t → byteAt t i = byteAt s (p + i))
    (hk0 : 0 ≤ k.val) (hkt : k.val ≤ (slen t : ℤ))
    (ans_s ans_t : Std.I64)
    (hs : character_replacement s k = ok ans_s) (ht : character_replacement t k = ok ans_t), ans_t.val ≤ ans_s.val) := by
  sorry

/-- Whenever the function returns a result ans, ans <= min(len(s), k + M), where M = max over all uppercase English letters c of |{ i | 0 <= i < len(s) and s[i] = c }| (and M = 0 when len(s)=0).
  Preconditions: Let n = len(s). Assume 0 <= n <= 100000, 0 <= k <= n, and for every i with 0 <= i < n, s[i] is an uppercase English letter (65 <= s[i] <= 90). -/
theorem spec_13 (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans) :
    ans.val ≤ min (slen s : ℤ) (k.val + (mf (bytes s) 0 (slen s) : ℤ)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hn : slen s ≤ 100000) (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (slen s : ℤ))
    (hupper : ∀ a ∈ bytes s, IsUppercaseByte a)
    (ans : Std.I64) (hans : character_replacement s k = ok ans), ans.val ≤ min (slen s : ℤ) (k.val + (mf (bytes s) 0 (slen s) : ℤ))) := by
  sorry

end AegisSpec.CharacterReplacement
