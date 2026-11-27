import Aegis.CountPrefixes.Code.Funs

/-!
# Specifications of `Aegis.CountPrefixes.count_prefixes`

LeetCode problem `count-prefixes-of-a-given-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPrefixes

def vecBytes (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map (fun b => b.val)

def sliceBytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def wordBytes (words : Slice (alloc.vec.Vec Std.U8)) : List (List Nat) :=
  words.val.map vecBytes

def IsPrefixOf (w s : List Nat) : Prop :=
  w.length ≤ s.length ∧ ∀ j : Nat, j < w.length → w[j]? = s[j]?

instance instDecidableIsPrefixOf (w s : List Nat) : Decidable (IsPrefixOf w s) := by
  unfold IsPrefixOf
  infer_instance

def countWhere (words : List (List Nat)) (p : List Nat → Bool) : Nat :=
  (words.filter p).length

def prefixCount (words : List (List Nat)) (s : List Nat) : Nat :=
  countWhere words (fun w => decide (IsPrefixOf w s))

def lengthLeCount (words : List (List Nat)) (s : List Nat) : Nat :=
  countWhere words (fun w => decide (w.length ≤ s.length))

def multiplicity (words : List (List Nat)) (x : List Nat) : Nat :=
  countWhere words (fun w => decide (w = x))

def distinctPrefixMultiplicitySum (words : List (List Nat)) (s : List Nat) : Nat :=
  ((words.dedup.filter (fun x => decide (IsPrefixOf x s))).map
    (fun x => multiplicity words x)).sum

def onlyWord (words : List (List Nat)) : List Nat := words.headD []

def wordAt (words : List (List Nat)) (i : Nat) : List Nat := (words[i]?).getD []

/-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < len(words) such that words[i] is a prefix of s. A byte array w is a prefix of s iff len(w) <= len(s) and for every j with 0 <= j < len(w), w[j] = s[j]. Equivalently, r = #{ i | 0 <= i < len(words) and len(words[i]) <= len(s) and (for every j with 0 <= j < len(words[i]), words[i][j] = s[j]) }. Each index is counted separately, so duplicate strings in words are counted once per occurrence.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_1
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val = ((prefixCount (wordBytes words) (sliceBytes s) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val = ((prefixCount (wordBytes words) (sliceBytes s) : Nat) : Int)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_2
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122) :
    ∃ r : Std.I64, Aegis.CountPrefixes.count_prefixes words s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122), ∃ r : Std.I64, Aegis.CountPrefixes.count_prefixes words s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_3
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(words).
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_4
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val ≤ ((wordBytes words).length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val ≤ ((wordBytes words).length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= the number of indices i with 0 <= i < len(words) and len(words[i]) <= len(s).
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_5
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val ≤ ((lengthLeCount (wordBytes words) (sliceBytes s) : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val ≤ ((lengthLeCount (wordBytes words) (sliceBytes s) : Nat) : Int)) := by
  sorry

/-- If len(words) = 1, then whenever the function returns r, r = 1 when words[0] is a prefix of s, and r = 0 otherwise. Here words[0] is a prefix of s iff len(words[0]) <= len(s) and for every j with 0 <= j < len(words[0]), words[0][j] = s[j].
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_6
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hwords : (wordBytes words).length = 1)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    (IsPrefixOf (onlyWord (wordBytes words)) (sliceBytes s) ∧ r.val = 1) ∨
      (¬ IsPrefixOf (onlyWord (wordBytes words)) (sliceBytes s) ∧ r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hwords : (wordBytes words).length = 1)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), (IsPrefixOf (onlyWord (wordBytes words)) (sliceBytes s) ∧ r.val = 1) ∨
      (¬ IsPrefixOf (onlyWord (wordBytes words)) (sliceBytes s) ∧ r.val = 0)) := by
  sorry

/-- If len(s) = 1, then whenever the function returns r, r equals the number of indices i with 0 <= i < len(words), len(words[i]) = 1, and words[i][0] = s[0].
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_7
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hs : (sliceBytes s).length = 1)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val = ((countWhere (wordBytes words)
      (fun w => decide (w.length = 1 ∧ w[0]? = (sliceBytes s)[0]?)) : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hs : (sliceBytes s).length = 1)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val = ((countWhere (wordBytes words)
      (fun w => decide (w.length = 1 ∧ w[0]? = (sliceBytes s)[0]?)) : Nat) : Int)) := by
  sorry

/-- If for every i with 0 <= i < len(words), len(words[i]) > len(s), then whenever the function returns r, r = 0.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_8
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hlong : ∀ w ∈ wordBytes words, (sliceBytes s).length < w.length)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hlong : ∀ w ∈ wordBytes words, (sliceBytes s).length < w.length)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val = 0) := by
  sorry

/-- If every word is a prefix of s, meaning that for every i with 0 <= i < len(words), len(words[i]) <= len(s) and for every j with 0 <= j < len(words[i]), words[i][j] = s[j], then whenever the function returns r, r = len(words).
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_9
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hall : ∀ w ∈ wordBytes words, IsPrefixOf w (sliceBytes s))
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val = ((wordBytes words).length : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hall : ∀ w ∈ wordBytes words, IsPrefixOf w (sliceBytes s))
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val = ((wordBytes words).length : Int)) := by
  sorry

/-- Whenever the function returns r, if k is the number of indices i with 0 <= i < len(words) and words[i] = s, then r >= k.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_10
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    ((multiplicity (wordBytes words) (sliceBytes s) : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), ((multiplicity (wordBytes words) (sliceBytes s) : Nat) : Int) ≤ r.val) := by
  sorry

/-- For every index i with 0 <= i < len(words) and len(words) >= 2, let words' be the slice obtained by deleting the i-th entry of words. Whenever the function returns r on (words, s) and returns r' on (words', s), we have r' = r - 1 if words[i] is a prefix of s (that is, len(words[i]) <= len(s) and for every j with 0 <= j < len(words[i]), words[i][j] = s[j]), and r' = r otherwise.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_11
    (words words' : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (r r' : Std.I64) (i : Nat)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hi : i < (wordBytes words).length)
    (hlen2 : 2 ≤ (wordBytes words).length)
    (hdel : wordBytes words' = (wordBytes words).eraseIdx i)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r)
    (hr' : Aegis.CountPrefixes.count_prefixes words' s = ok r') :
    (IsPrefixOf (wordAt (wordBytes words) i) (sliceBytes s) ∧ r'.val = r.val - 1) ∨
      (¬ IsPrefixOf (wordAt (wordBytes words) i) (sliceBytes s) ∧ r'.val = r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (r r' : Std.I64) (i : Nat)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hi : i < (wordBytes words).length)
    (hlen2 : 2 ≤ (wordBytes words).length)
    (hdel : wordBytes words' = (wordBytes words).eraseIdx i)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r)
    (hr' : Aegis.CountPrefixes.count_prefixes words' s = ok r'), (IsPrefixOf (wordAt (wordBytes words) i) (sliceBytes s) ∧ r'.val = r.val - 1) ∨
      (¬ IsPrefixOf (wordAt (wordBytes words) i) (sliceBytes s) ∧ r'.val = r.val)) := by
  sorry

/-- For every permutation pi of the index set {0, ..., len(words)-1}, let words_pi be the slice of length len(words) with words_pi[i] = words[pi(i)] for every i with 0 <= i < len(words). Whenever the function returns r on (words, s) and returns r_pi on (words_pi, s), r = r_pi.
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_12
    (words words' : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (r r' : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hperm : (wordBytes words').Perm (wordBytes words))
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r)
    (hr' : Aegis.CountPrefixes.count_prefixes words' s = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8)
    (r r' : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hperm : (wordBytes words').Perm (wordBytes words))
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r)
    (hr' : Aegis.CountPrefixes.count_prefixes words' s = ok r'), r.val = r'.val) := by
  sorry

/-- For each byte array x, let m(x) be the number of indices i with 0 <= i < len(words) and words[i] = x. Whenever the function returns r, r equals the sum of m(x) over all distinct byte arrays x that occur in words and are prefixes of s, where x is a prefix of s iff len(x) <= len(s) and for every j with 0 <= j < len(x), x[j] = s[j].
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_13
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val =
      ((distinctPrefixMultiplicitySum (wordBytes words) (sliceBytes s) : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val =
      ((distinctPrefixMultiplicitySum (wordBytes words) (sliceBytes s) : Nat) : Int)) := by
  sorry

/-- If for every i with 0 <= i < len(words), len(words[i]) = 1, then whenever the function returns r, r equals the number of indices i with 0 <= i < len(words) and words[i][0] = s[0].
  Preconditions: words is a slice with 1 <= len(words) <= 1000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 10; 1 <= len(s) <= 10; every byte of every words[i] and of s is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_14
    (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hunit : ∀ w ∈ wordBytes words, w.length = 1)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r) :
    r.val = ((countWhere (wordBytes words)
      (fun w => decide (w[0]? = (sliceBytes s)[0]?)) : Nat) : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (s : Slice Std.U8) (r : Std.I64)
    (hlen : 1 ≤ (wordBytes words).length ∧ (wordBytes words).length ≤ 1000)
    (hwlen : ∀ w ∈ wordBytes words, 1 ≤ w.length ∧ w.length ≤ 10)
    (hslen : 1 ≤ (sliceBytes s).length ∧ (sliceBytes s).length ≤ 10)
    (hwbytes : ∀ w ∈ wordBytes words, ∀ b ∈ w, 97 ≤ b ∧ b ≤ 122)
    (hsbytes : ∀ b ∈ sliceBytes s, 97 ≤ b ∧ b ≤ 122)
    (hunit : ∀ w ∈ wordBytes words, w.length = 1)
    (hr : Aegis.CountPrefixes.count_prefixes words s = ok r), r.val = ((countWhere (wordBytes words)
      (fun w => decide (w[0]? = (sliceBytes s)[0]?)) : Nat) : Int)) := by
  sorry

end AegisSpec.CountPrefixes
