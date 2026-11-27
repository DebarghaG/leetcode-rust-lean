import Aegis.CountPrefixSuffixPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPrefixSuffixPairs.count_prefix_suffix_pairs`

LeetCode problem `count-prefix-and-suffix-pairs-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountPrefixSuffixPairs (count_prefix_suffix_pairs)

namespace AegisSpec.CountPrefixSuffixPairs

def wordAt (words : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
  (words.val.getD i default).val

def wordLists (words : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  words.val.map (fun v => v.val)

def isPrefix (a b : List Std.U8) : Bool :=
  decide (a.length ≤ b.length) && (b.take a.length) == a

def IsPrefix (a b : List Std.U8) : Prop := isPrefix a b = true

def isSuffix (a b : List Std.U8) : Bool :=
  decide (a.length ≤ b.length) && (b.drop (b.length - a.length)) == a

def IsSuffix (a b : List Std.U8) : Prop := isSuffix a b = true

def IsPrefixAndSuffix (a b : List Std.U8) : Prop := IsPrefix a b ∧ IsSuffix a b

def pairCount (ws : List (List Std.U8)) (p : List Std.U8 → List Std.U8 → Bool) : Nat :=
  ((List.range ws.length).product (List.range ws.length)).countP
    (fun ij => decide (ij.1 < ij.2) && p (ws.getD ij.1 []) (ws.getD ij.2 []))

def goodPairCount (ws : List (List Std.U8)) : Nat :=
  pairCount ws (fun a b => isPrefix a b && isSuffix a b)

def equalPairCount (ws : List (List Std.U8)) : Nat :=
  pairCount ws (fun a b => decide (a = b))

def lenLePairCount (ws : List (List Std.U8)) : Nat :=
  pairCount ws (fun a b => decide (a.length ≤ b.length))

def prefixPairCount (ws : List (List Std.U8)) : Nat :=
  pairCount ws (fun a b => isPrefix a b)

def countPreSufOf (ws : List (List Std.U8)) (c : List Std.U8) (j : Nat) : Nat :=
  ((List.range j).countP fun i => isPrefix (ws.getD i []) c && isSuffix (ws.getD i []) c)

def goodPairSum (ws : List (List Std.U8)) : Nat :=
  ((List.range ws.length).map (fun j => countPreSufOf ws (ws.getD j []) j)).sum

def countWordsPreSufOf (ws : List (List Std.U8)) (w : List Std.U8) : Nat :=
  ws.countP (fun a => isPrefix w a && isSuffix w a)

def pairBound (n : Nat) : Nat := n * (n - 1) / 2

def InputConstraints (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ words.val.length ∧
  words.val.length ≤ 100000 ∧
  (∀ i, i < words.val.length →
    1 ≤ (wordAt words i).length ∧ (wordAt words i).length ≤ 100000 ∧
      ∀ b ∈ wordAt words i, 97 ≤ b.val ∧ b.val ≤ 122) ∧
  (words.val.map (fun v => v.val.length)).sum ≤ 500000

/-- Let n = len(words). Define a pair (i,j) to be good iff 0 <= i < j < n and words[i] is both a prefix and a suffix of words[j], where a string a is a prefix of a string b iff len(a) <= len(b) and a[k] = b[k] for every 0 <= k < len(a), and a is a suffix of b iff len(a) <= len(b) and a[k] = b[len(b)-len(a)+k] for every 0 <= k < len(a). Whenever count_prefix_suffix_pairs(words) returns a result r, r equals the number of good pairs (i,j).
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val = ((goodPairCount (wordLists words) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val = ((goodPairCount (wordLists words) : Nat) : Int)) := by
  sorry

/-- The function count_prefix_suffix_pairs(words) returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words) :
    ∃ r : I64, count_prefix_suffix_pairs words = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words), ∃ r : I64, count_prefix_suffix_pairs words = ok r) := by
  sorry

/-- Let n = len(words). Whenever the function returns a result r, 0 <= r <= n*(n-1)/2.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((pairBound words.val.length : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), 0 ≤ r.val ∧ r.val ≤ ((pairBound words.val.length : Nat) : Int)) := by
  sorry

/-- Let L = #{ (i,j) | 0 <= i < j < len(words) and len(words[i]) <= len(words[j]) }. Whenever the function returns a result r, r <= L.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val ≤ ((lenLePairCount (wordLists words) : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val ≤ ((lenLePairCount (wordLists words) : Nat) : Int)) := by
  sorry

/-- Let E = #{ (i,j) | 0 <= i < j < len(words) and words[i] = words[j] }. Whenever the function returns a result r, r >= E.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    ((equalPairCount (wordLists words) : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), ((equalPairCount (wordLists words) : Nat) : Int) ≤ r.val) := by
  sorry

/-- Let P = #{ (i,j) | 0 <= i < j < len(words) and words[i] is a prefix of words[j] }, where a string a is a prefix of a string b iff len(a) <= len(b) and a[k] = b[k] for every 0 <= k < len(a). Whenever the function returns a result r, r <= P.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val ≤ ((prefixPairCount (wordLists words) : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val ≤ ((prefixPairCount (wordLists words) : Nat) : Int)) := by
  sorry

/-- If words[i] = words[0] for every 0 <= i < len(words) (so all words are the same nonempty string), then whenever the function returns a result r, r = len(words)*(len(words)-1)/2.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hall : ∀ i, i < words.val.length → wordAt words i = wordAt words 0)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val = ((pairBound words.val.length : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hall : ∀ i, i < words.val.length → wordAt words i = wordAt words 0)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val = ((pairBound words.val.length : Nat) : Int)) := by
  sorry

/-- If len(words[0]) > len(words[1]) > ... > len(words[len(words)-1]) (the lengths are strictly decreasing with index), then whenever the function returns a result r, r = 0.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hdec : ∀ i j, i < j → j < words.val.length →
      (wordAt words j).length < (wordAt words i).length)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hdec : ∀ i j, i < j → j < words.val.length →
      (wordAt words j).length < (wordAt words i).length)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val = 0) := by
  sorry

/-- If len(words[i]) = 1 for every 0 <= i < len(words), then whenever the function returns a result r, r = #{ (i,j) | 0 <= i < j < len(words) and words[i] = words[j] }.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hall : ∀ i, i < words.val.length → (wordAt words i).length = 1)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val = ((equalPairCount (wordLists words) : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hall : ∀ i, i < words.val.length → (wordAt words i).length = 1)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val = ((equalPairCount (wordLists words) : Nat) : Int)) := by
  sorry

/-- If all words have equal length (len(words[i]) = len(words[0]) for every 0 <= i < len(words)) and words[i] != words[j] for every 0 <= i < j < len(words), then whenever the function returns a result r, r = 0.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hlen : ∀ i, i < words.val.length → (wordAt words i).length = (wordAt words 0).length)
    (hne : ∀ i j, i < j → j < words.val.length → wordAt words i ≠ wordAt words j)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hlen : ∀ i, i < words.val.length → (wordAt words i).length = (wordAt words 0).length)
    (hne : ∀ i j, i < j → j < words.val.length → wordAt words i ≠ wordAt words j)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val = 0) := by
  sorry

/-- Whenever count_prefix_suffix_pairs(words) returns r and count_prefix_suffix_pairs(words') returns r', r = r'.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. Additionally, words' is a slice of byte vectors with len(words') = len(words), and for every 0 <= i < len(words), len(words'[i]) = len(words[i]) and words'[i][k] = words[i][len(words[i])-1-k] for every 0 <= k < len(words[i]). -/
theorem spec_11 (words words' : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hlen : words'.val.length = words.val.length)
    (hrev : ∀ i, i < words.val.length → wordAt words' i = (wordAt words i).reverse)
    (r r' : I64) (hr : count_prefix_suffix_pairs words = ok r)
    (hr' : count_prefix_suffix_pairs words' = ok r') :
    r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (hlen : words'.val.length = words.val.length)
    (hrev : ∀ i, i < words.val.length → wordAt words' i = (wordAt words i).reverse)
    (r r' : I64) (hr : count_prefix_suffix_pairs words = ok r)
    (hr' : count_prefix_suffix_pairs words' = ok r'), r = r') := by
  sorry

/-- Let C = #{ i | 0 <= i < len(words) and words[i] is both a prefix and a suffix of w }, where a string a is a prefix of b iff len(a) <= len(b) and a[k] = b[k] for every 0 <= k < len(a), and a is a suffix of b iff len(a) <= len(b) and a[k] = b[len(b)-len(a)+k] for every 0 <= k < len(a). Whenever count_prefix_suffix_pairs(words) returns r and count_prefix_suffix_pairs(words') returns r', r' = r + C.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. Additionally, w is a nonempty byte string of lowercase ASCII letters (bytes in 97..122); words' is a slice of byte vectors with len(words') = len(words)+1, words'[i] = words[i] for 0 <= i < len(words), words'[len(words)] = w, and words' also satisfies the problem constraints. -/
theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (w : List Std.U8) (hwlen : 1 ≤ w.length) (hw : ∀ b ∈ w, 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8)) (hcon' : InputConstraints words')
    (hwords' : wordLists words' = wordLists words ++ [w])
    (r r' : I64) (hr : count_prefix_suffix_pairs words = ok r)
    (hr' : count_prefix_suffix_pairs words' = ok r') :
    r' = r + ((countPreSufOf (wordLists words) w (wordLists words).length : Nat) : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (w : List Std.U8) (hwlen : 1 ≤ w.length) (hw : ∀ b ∈ w, 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8)) (hcon' : InputConstraints words')
    (hwords' : wordLists words' = wordLists words ++ [w])
    (r r' : I64) (hr : count_prefix_suffix_pairs words = ok r)
    (hr' : count_prefix_suffix_pairs words' = ok r'), r' = r + ((countPreSufOf (wordLists words) w (wordLists words).length : Nat) : Int)) := by
  sorry

/-- Let C = #{ j | 0 <= j < len(words) and w is both a prefix and a suffix of words[j] }, where a string a is a prefix of b iff len(a) <= len(b) and a[k] = b[k] for every 0 <= k < len(a), and a is a suffix of b iff len(a) <= len(b) and a[k] = b[len(b)-len(a)+k] for every 0 <= k < len(a). Whenever count_prefix_suffix_pairs(words) returns r and count_prefix_suffix_pairs(words') returns r', r' = r + C.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. Additionally, w is a nonempty byte string of lowercase ASCII letters (bytes in 97..122); words' is a slice of byte vectors with len(words') = len(words)+1, words'[0] = w, words'[i+1] = words[i] for 0 <= i < len(words), and words' also satisfies the problem constraints. -/
theorem spec_13 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (w : List Std.U8) (hwlen : 1 ≤ w.length) (hw : ∀ b ∈ w, 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8)) (hcon' : InputConstraints words')
    (hwords' : wordLists words' = w :: wordLists words)
    (r r' : I64) (hr : count_prefix_suffix_pairs words = ok r)
    (hr' : count_prefix_suffix_pairs words' = ok r') :
    r' = r + ((countWordsPreSufOf (wordLists words) w : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (w : List Std.U8) (hwlen : 1 ≤ w.length) (hw : ∀ b ∈ w, 97 ≤ b.val ∧ b.val ≤ 122)
    (words' : Slice (alloc.vec.Vec Std.U8)) (hcon' : InputConstraints words')
    (hwords' : wordLists words' = w :: wordLists words)
    (r r' : I64) (hr : count_prefix_suffix_pairs words = ok r)
    (hr' : count_prefix_suffix_pairs words' = ok r'), r' = r + ((countWordsPreSufOf (wordLists words) w : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exists an index pair (i,j) with 0 <= i < j < len(words) such that words[i] is both a prefix and a suffix of words[j], where a string a is a prefix of b iff len(a) <= len(b) and a[k] = b[k] for every 0 <= k < len(a), and a is a suffix of b iff len(a) <= len(b) and a[k] = b[len(b)-len(a)+k] for every 0 <= k < len(a).
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_14 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    0 < r.val ↔ ∃ i j, i < j ∧ j < words.val.length ∧
      IsPrefixAndSuffix (wordAt words i) (wordAt words j) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), 0 < r.val ↔ ∃ i j, i < j ∧ j < words.val.length ∧
      IsPrefixAndSuffix (wordAt words i) (wordAt words j)) := by
  sorry

/-- Let n = len(words). For each j with 0 <= j < n, let c_j = #{ i | 0 <= i < j and words[i] is both a prefix and a suffix of words[j] }, where a string a is a prefix of b iff len(a) <= len(b) and a[k] = b[k] for every 0 <= k < len(a), and a is a suffix of b iff len(a) <= len(b) and a[k] = b[len(b)-len(a)+k] for every 0 <= k < len(a). Whenever the function returns a result r, r = sum_{j=0}^{n-1} c_j.
  Preconditions: words is a slice of byte vectors satisfying the problem constraints: 1 <= len(words) <= 100000; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 100000 and every byte of words[i] is in 97..122; and sum_{i=0}^{len(words)-1} len(words[i]) <= 500000. -/
theorem spec_15 (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r) :
    r.val = ((goodPairSum (wordLists words) : Nat) : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (hcon : InputConstraints words)
    (r : I64) (hr : count_prefix_suffix_pairs words = ok r), r.val = ((goodPairSum (wordLists words) : Nat) : Int)) := by
  sorry

end AegisSpec.CountPrefixSuffixPairs
