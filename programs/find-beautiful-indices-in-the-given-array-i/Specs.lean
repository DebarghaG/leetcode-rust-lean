import Aegis.BeautifulIndices.Code.Funs

/-!
# Specifications of `Aegis.BeautifulIndices.beautiful_indices`

LeetCode problem `find-beautiful-indices-in-the-given-array-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BeautifulIndices

def getByte (s : List Std.U8) (i : ℤ) : Option Std.U8 := s[i.toNat]?

def OccursAt (s pat : List Std.U8) (i : ℤ) : Prop :=
  ∀ t : ℕ, t < pat.length → getByte s (i + (t : ℤ)) = getByte pat (t : ℤ)

def IsAMatch (s a : List Std.U8) (i : ℤ) : Prop :=
  0 ≤ i ∧ i + (a.length : ℤ) ≤ (s.length : ℤ) ∧ OccursAt s a i

def IsBMatch (s b : List Std.U8) (j : ℤ) : Prop :=
  0 ≤ j ∧ j + (b.length : ℤ) ≤ (s.length : ℤ) ∧ OccursAt s b j

def IsBeautiful (s a b : List Std.U8) (k i : ℤ) : Prop :=
  IsAMatch s a i ∧ ∃ j : ℤ, IsBMatch s b j ∧ |j - i| ≤ k

def OccursIn (r : List Std.I64) (i : ℤ) : Prop :=
  ∃ t : ℕ, ∃ ht : t < r.length, (r[t]'ht).val = i

def StrictlyIncreasing (r : List Std.I64) : Prop :=
  ∀ (t : ℕ) (ht : t + 1 < r.length),
    (r[t]'(Nat.lt_of_succ_lt ht)).val < (r[t + 1]'ht).val

def Lowercase (l : List Std.U8) : Prop :=
  ∀ x ∈ l, 97 ≤ x.val ∧ x.val ≤ 122

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a (i.e., s[i+t] = a[t] for every t with 0 <= t < la); an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b (i.e., s[j+t] = b[t] for every t with 0 <= t < lb); and i is beautiful if i is an a-match and there exists a b-match j with |j - i| <= k. The function returns a result r (a Vec of i64) such that: (a) for every integer i, i occurs in r (i.e., there is t with 0 <= t < len(r) and r[t] = i) iff i is beautiful; and (b) for every t with 0 <= t and t+1 < len(r), r[t] < r[t+1]. Equivalently, r is exactly the strictly increasing list of all beautiful indices.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_1 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.BeautifulIndices.beautiful_indices s a b k = ok r ∧
        (∀ i : ℤ, OccursIn r.val i ↔ IsBeautiful s.val a.val b.val k.val i) ∧
          StrictlyIncreasing r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.BeautifulIndices.beautiful_indices s a b k = ok r ∧
        (∀ i : ℤ, OccursIn r.val i ↔ IsBeautiful s.val a.val b.val k.val i) ∧
          StrictlyIncreasing r.val) := by
  sorry

/-- The function returns a result r (a Vec of i64) for every input satisfying the preconditions; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_2 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b; and i is beautiful if i is an a-match and there exists a b-match j with |j - i| <= k. Whenever the function returns a result r, for every t with 0 <= t < len(r), the integer r[t] is beautiful.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_3 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length),
        IsBeautiful s.val a.val b.val k.val (r.val[t]'ht).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length),
        IsBeautiful s.val a.val b.val k.val (r.val[t]'ht).val) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b; and i is beautiful if i is an a-match and there exists a b-match j with |j - i| <= k. Whenever the function returns a result r, for every integer i, if i is beautiful then i occurs in r (there exists t with 0 <= t < len(r) and r[t] = i).
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_4 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ i : ℤ, IsBeautiful s.val a.val b.val k.val i → OccursIn r.val i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ i : ℤ, IsBeautiful s.val a.val b.val k.val i → OccursIn r.val i) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t and t+1 < len(r), r[t] < r[t+1].
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_5 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      StrictlyIncreasing r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      StrictlyIncreasing r.val) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < len(r), 0 <= r[t] and r[t] + la <= n.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_6 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length),
        0 ≤ (r.val[t]'ht).val ∧ (r.val[t]'ht).val + (a.val.length : ℤ) ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length),
        0 ≤ (r.val[t]'ht).val ∧ (r.val[t]'ht).val + (a.val.length : ℤ) ≤ (s.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= (if la <= n then n - la + 1 else 0).
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_7 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      r.val.length ≤
        (if a.val.length ≤ s.val.length then s.val.length - a.val.length + 1 else 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      r.val.length ≤
        (if a.val.length ≤ s.val.length then s.val.length - a.val.length + 1 else 0)) := by
  sorry

/-- Throughout this statement, an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b. Whenever the function returns a result r, for every t with 0 <= t < len(r), there exists a b-match j such that |j - r[t]| <= k.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_8 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length),
        ∃ j : ℤ, IsBMatch s.val b.val j ∧ |j - (r.val[t]'ht).val| ≤ k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length),
        ∃ j : ℤ, IsBMatch s.val b.val j ∧ |j - (r.val[t]'ht).val| ≤ k.val) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a. Whenever the function returns a result r, for every t with 0 <= t < len(r), r[t] is an a-match.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_9 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length), IsAMatch s.val a.val (r.val[t]'ht).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ (t : ℕ) (ht : t < r.val.length), IsAMatch s.val a.val (r.val[t]'ht).val) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a. Whenever the function returns a result r, if there is no a-match integer i, then len(r) = 0.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_10 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      (∀ i : ℤ, ¬ IsAMatch s.val a.val i) → r.val.length = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      (∀ i : ℤ, ¬ IsAMatch s.val a.val i) → r.val.length = 0) := by
  sorry

/-- Throughout this statement, an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b. Whenever the function returns a result r, if there is no b-match integer j, then len(r) = 0.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_11 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      (∀ j : ℤ, ¬ IsBMatch s.val b.val j) → r.val.length = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      (∀ j : ℤ, ¬ IsBMatch s.val b.val j) → r.val.length = 0) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b. Whenever the function returns a result r, if k >= n - 1 and there exists at least one b-match, then for every integer i, i occurs in r (there is t with 0 <= t < len(r) and r[t] = i) iff i is an a-match.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_12 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      (s.val.length : ℤ) - 1 ≤ k.val →
        (∃ j : ℤ, IsBMatch s.val b.val j) →
          ∀ i : ℤ, OccursIn r.val i ↔ IsAMatch s.val a.val i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      (s.val.length : ℤ) - 1 ≤ k.val →
        (∃ j : ℤ, IsBMatch s.val b.val j) →
          ∀ i : ℤ, OccursIn r.val i ↔ IsAMatch s.val a.val i) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b. Whenever the function returns a result r on input with parameter k, for every integer k' with k <= k' <= n, every integer i occurring in r is beautiful for the parameter k' (i.e., i is an a-match and there exists a b-match j with |j - i| <= k').
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_13 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ k' : ℤ, k.val ≤ k' → k' ≤ (s.val.length : ℤ) →
        ∀ i : ℤ, OccursIn r.val i → IsBeautiful s.val a.val b.val k' i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      ∀ k' : ℤ, k.val ≤ k' → k' ≤ (s.val.length : ℤ) →
        ∀ i : ℤ, OccursIn r.val i → IsBeautiful s.val a.val b.val k' i) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b; and i is beautiful if i is an a-match and there exists a b-match j with |j - i| <= k. Whenever the function returns a result r and len(r) > 0, there is no beautiful integer i with i < r[0].
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_14 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      0 < r.val.length → ∀ x : Std.I64, r.val[0]? = some x →
        ∀ i : ℤ, IsBeautiful s.val a.val b.val k.val i → x.val ≤ i := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      0 < r.val.length → ∀ x : Std.I64, r.val[0]? = some x →
        ∀ i : ℤ, IsBeautiful s.val a.val b.val k.val i → x.val ≤ i) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b; and i is beautiful if i is an a-match and there exists a b-match j with |j - i| <= k. Whenever the function returns a result r and len(r) > 0, there is no beautiful integer i with i > r[len(r)-1].
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_15 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      0 < r.val.length → ∀ x : Std.I64, r.val[r.val.length - 1]? = some x →
        ∀ i : ℤ, IsBeautiful s.val a.val b.val k.val i → i ≤ x.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      0 < r.val.length → ∀ x : Std.I64, r.val[r.val.length - 1]? = some x →
        ∀ i : ℤ, IsBeautiful s.val a.val b.val k.val i → i ≤ x.val) := by
  sorry

/-- Throughout this statement, an integer i is an a-match if 0 <= i, i + la <= n, and s[i..i+la-1] = a; an integer j is a b-match if 0 <= j, j + lb <= n, and s[j..j+lb-1] = b; and i is beautiful if i is an a-match and there exists a b-match j with |j - i| <= k. Whenever the function returns a result r, len(r) is the number of integers i that are beautiful.
  Preconditions: Let n = len(s), la = len(a), lb = len(b). The input satisfies n <= 100000, 1 <= n, k is an i64 with 1 <= k <= n, 1 <= la <= 10, 1 <= lb <= 10, and every byte of s, a, and b is in the ASCII range 97..122 (lowercase English letters). No relation la <= n or lb <= n is assumed. All indices below are mathematical integers and all string/slice indexing is 0-based. -/
theorem spec_16 (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      r.val.length = Nat.card {i : ℤ // IsBeautiful s.val a.val b.val k.val i} := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s a b : Slice Std.U8) (k : Std.I64)
    (hn : s.val.length ≤ 100000) (hnpos : 1 ≤ s.val.length)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ (s.val.length : ℤ))
    (hlapos : 1 ≤ a.val.length) (hlale : a.val.length ≤ 10)
    (hlbpos : 1 ≤ b.val.length) (hlble : b.val.length ≤ 10)
    (hs : Lowercase s.val) (ha : Lowercase a.val) (hb : Lowercase b.val), ∀ r : alloc.vec.Vec Std.I64, Aegis.BeautifulIndices.beautiful_indices s a b k = ok r →
      r.val.length = Nat.card {i : ℤ // IsBeautiful s.val a.val b.val k.val i}) := by
  sorry

end AegisSpec.BeautifulIndices
