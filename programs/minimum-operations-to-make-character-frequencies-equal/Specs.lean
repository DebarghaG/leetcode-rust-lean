import Aegis.MakeStringGood.Code.Funs

/-!
# Specifications of `Aegis.MakeStringGood.make_string_good`

LeetCode problem `minimum-operations-to-make-character-frequencies-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MakeStringGood (make_string_good)

namespace AegisSpec.MakeStringGood

def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

def IsLower (c : ℕ) : Prop := 97 ≤ c ∧ c ≤ 122

def IsLowerStr (t : List ℕ) : Prop := ∀ c ∈ t, IsLower c

def occ : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: xs, c => (if x = c then 1 else 0) + occ xs c

def occS (s : Slice Std.U8) (c : ℕ) : ℕ := occ (bytes s) c

def Good (t : List ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ c : ℕ, IsLower c → occ t c = 0 ∨ occ t c = k

def GoodStr (t : List ℕ) : Prop := t ≠ [] ∧ IsLowerStr t ∧ Good t

inductive Step : List ℕ → List ℕ → Prop where
  | del (l₁ l₂ : List ℕ) (c : ℕ) : Step (l₁ ++ c :: l₂) (l₁ ++ l₂)
  | ins (l₁ l₂ : List ℕ) (c : ℕ) (hc : IsLower c) : Step (l₁ ++ l₂) (l₁ ++ c :: l₂)
  | succ (l₁ l₂ : List ℕ) (c : ℕ) (hc₁ : 97 ≤ c) (hc₂ : c ≤ 121) :
      Step (l₁ ++ c :: l₂) (l₁ ++ (c + 1) :: l₂)

inductive Steps : List ℕ → List ℕ → ℕ → Prop where
  | refl (l : List ℕ) : Steps l l 0
  | step {a b c : List ℕ} {n : ℕ} : Step a b → Steps b c n → Steps a c (n + 1)

def absDiff (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

def sumAbsDiffTo (t : List ℕ) (k : ℕ) : ℕ :=
  ((List.range 26).map (fun i => if occ t (97 + i) = 0 then 0 else absDiff (occ t (97 + i)) k)).sum

/-- Whenever make_string_good returns a result r on an input s satisfying the preconditions, r is the smallest nonnegative integer for which there exist a nonempty string t over the lowercase English letters and a sequence of exactly r allowed operations that transforms s into t. An allowed operation is: delete one character; insert one lowercase English letter at any position; or replace one occurrence of a letter c by c+1, for c from 'a' through 'y'. The target t is good, meaning there is an integer k > 0 such that for every lowercase letter c, the number of occurrences of c in t is either 0 or k.
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r) :
    0 ≤ r.val ∧
      (∃ t : List ℕ, GoodStr t ∧ Steps (bytes s) t r.val.toNat) ∧
      (∀ (q : ℕ) (t : List ℕ), GoodStr t → Steps (bytes s) t q → r.val.toNat ≤ q) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r), 0 ≤ r.val ∧
      (∃ t : List ℕ, GoodStr t ∧ Steps (bytes s) t r.val.toNat) ∧
      (∀ (q : ℕ) (t : List ℕ), GoodStr t → Steps (bytes s) t q → r.val.toNat ≤ q)) := by
  sorry

/-- For every s satisfying the preconditions, make_string_good returns a result r; it does not panic, go out of bounds, overflow, or otherwise fail.
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val) :
    ∃ r : Std.I64, make_string_good s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val), ∃ r : Std.I64, make_string_good s = ok r) := by
  sorry

/-- Whenever make_string_good returns a result r on such an s, r = 0 if and only if s is good, meaning there exists an integer k > 0 such that for every lowercase letter c, occ_s(c) is either 0 or k.
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). Let occ_s(c) be the number of indices i with 0 <= i < len(s) and s[i] equal to c. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r) :
    r.val = 0 ↔ Good (bytes s) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r), r.val = 0 ↔ Good (bytes s)) := by
  sorry

/-- Whenever make_string_good returns r1 on s1 and r2 on s2, we have r1 = r2. In particular, permuting the characters of s does not change the result.
  Preconditions: 3 <= len(s1), len(s2) <= 20000, every character of s1 and s2 is a lowercase English letter, and for every lowercase letter c, the number of occurrences of c in s1 equals the number of occurrences of c in s2. -/
theorem spec_4 (s1 s2 : Slice Std.U8)
    (hlen1_lo : 3 ≤ s1.val.length) (hlen1_hi : s1.val.length ≤ 20000)
    (hlen2_lo : 3 ≤ s2.val.length) (hlen2_hi : s2.val.length ≤ 20000)
    (hlower1 : ∀ b ∈ s1.val, IsLower b.val) (hlower2 : ∀ b ∈ s2.val, IsLower b.val)
    (hocc : ∀ c : ℕ, IsLower c → occS s1 c = occS s2 c)
    (r1 r2 : Std.I64) (h1 : make_string_good s1 = ok r1) (h2 : make_string_good s2 = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8)
    (hlen1_lo : 3 ≤ s1.val.length) (hlen1_hi : s1.val.length ≤ 20000)
    (hlen2_lo : 3 ≤ s2.val.length) (hlen2_hi : s2.val.length ≤ 20000)
    (hlower1 : ∀ b ∈ s1.val, IsLower b.val) (hlower2 : ∀ b ∈ s2.val, IsLower b.val)
    (hocc : ∀ c : ℕ, IsLower c → occS s1 c = occS s2 c)
    (r1 r2 : Std.I64) (h1 : make_string_good s1 = ok r1) (h2 : make_string_good s2 = ok r2), r1 = r2) := by
  sorry

/-- Whenever make_string_good returns a result r on such an s, there exist a nonempty good string t over the lowercase English letters and a sequence of exactly r allowed operations that transforms s into t, where allowed operations are delete one character, insert one lowercase English letter, and replace one occurrence of c by c+1 for c from 'a' through 'y'.
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r) :
    ∃ t : List ℕ, GoodStr t ∧ Steps (bytes s) t r.val.toNat := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r), ∃ t : List ℕ, GoodStr t ∧ Steps (bytes s) t r.val.toNat) := by
  sorry

/-- Whenever make_string_good returns a result r on such an s, for every nonempty good string t over the lowercase English letters and every sequence of q allowed operations that transforms s into t, where allowed operations are delete one character, insert one lowercase English letter, and replace one occurrence of c by c+1 for c from 'a' through 'y', we have r <= q.
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r) :
    ∀ (t : List ℕ) (q : ℕ), GoodStr t → Steps (bytes s) t q → r.val ≤ (q : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r), ∀ (t : List ℕ) (q : ℕ), GoodStr t → Steps (bytes s) t q → r.val ≤ (q : ℤ)) := by
  sorry

/-- Whenever make_string_good returns a result r on such an s, for every lowercase letter c with occ_s(c) > 0, we have r <= len(s) - occ_s(c).
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). Let occ_s(c) be the number of occurrences of c in s. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r) :
    ∀ c : ℕ, IsLower c → 0 < occS s c →
      r.val ≤ (s.val.length : ℤ) - (occS s c : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r), ∀ c : ℕ, IsLower c → 0 < occS s c →
      r.val ≤ (s.val.length : ℤ) - (occS s c : ℤ)) := by
  sorry

/-- Whenever make_string_good returns a result r on such an s, for every integer k with 1 <= k <= len(s), we have r <= sum over lowercase letters c with occ_s(c) > 0 of |occ_s(c) - k|.
  Preconditions: 3 <= len(s) <= 20000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter ('a' through 'z'). Let occ_s(c) be the number of occurrences of c in s. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r) :
    ∀ k : ℕ, 1 ≤ k → k ≤ s.val.length → r.val ≤ (sumAbsDiffTo (bytes s) k : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (hlower : ∀ b ∈ s.val, IsLower b.val)
    (r : Std.I64) (h : make_string_good s = ok r), ∀ k : ℕ, 1 ≤ k → k ≤ s.val.length → r.val ≤ (sumAbsDiffTo (bytes s) k : ℤ)) := by
  sorry

end AegisSpec.MakeStringGood
