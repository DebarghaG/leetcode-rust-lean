import Aegis.TopKFrequent.Code.Funs

/-!
# Specifications of `Aegis.TopKFrequent.top_k_frequent`

LeetCode problem `top-k-frequent-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TopKFrequent

  open Aegis.TopKFrequent (top_k_frequent)

  abbrev Word := alloc.vec.Vec Std.U8

  def lexBytesB : List Std.U8 → List Std.U8 → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | a :: xs, b :: ys =>
      if a.val < b.val then true else if b.val < a.val then false else lexBytesB xs ys

  def lexBytes (x y : List Std.U8) : Prop := lexBytesB x y = true

  instance instDecidableLexBytes (x y : List Std.U8) : Decidable (lexBytes x y) :=
    inferInstanceAs (Decidable (lexBytesB x y = true))

  def freq (words : List Word) (w : Word) : Nat :=
    (words.filter (fun u => u.val = w.val)).length

  def freqBytes (words : List Word) (w : List Std.U8) : Nat :=
    (words.filter (fun u => u.val = w)).length

  def occursIn (words : List Word) (v : Word) : Prop :=
    ∃ (i : Nat) (u : Word), words[i]? = some u ∧ u.val = v.val

  def distinctBytes (words : List Word) : List (List Std.U8) :=
    (words.map (fun u => u.val)).dedup

  def numDistinct (words : List Word) : Nat := (distinctBytes words).length

  def precedesB (words : List Word) (v w : List Std.U8) : Bool :=
    freqBytes words w < freqBytes words v ||
      (freqBytes words v == freqBytes words w && lexBytesB v w)

  def precedes (words : List Word) (v w : Word) : Prop :=
    freq words v > freq words w ∨ (freq words v = freq words w ∧ lexBytes v.val w.val)

  instance instDecidablePrecedes (words : List Word) (v w : Word) : Decidable (precedes words v w) :=
    inferInstanceAs
      (Decidable (freq words v > freq words w ∨
        (freq words v = freq words w ∧ lexBytes v.val w.val)))

  def numPreceding (words : List Word) (w : List Std.U8) : Nat :=
    ((distinctBytes words).filter (fun b => precedesB words b w)).length

  /-- Whenever the function returns a result r, r is exactly the top-k list: (a) len(r) = k; (b) for every j with 0 <= j < len(r), r[j] occurs in words; (c) the entries of r are pairwise distinct; (d) for every i,j with 0 <= i < j < len(r), r[i] precedes r[j]; (e) for every word w that occurs in words and is not equal to any entry of r, r[len(r)-1] precedes w. Here precedes, freq, and lex are as defined in the preconditions.
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_1
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :

      r.val.length = k.val.toNat ∧

      (∀ (j : Nat) (v : Word), j < r.val.length → r.val[j]? = some v →
        occursIn words.val v) ∧

      (∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
        r.val[i]? = some vi → r.val[j]? = some vj → vi.val ≠ vj.val) ∧

      (∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
        r.val[i]? = some vi → r.val[j]? = some vj → precedes words.val vi vj) ∧

      (∀ (v w : Word), occursIn words.val w → (∀ e ∈ r.val, e.val ≠ w.val) →
        r.val[r.val.length - 1]? = some v → precedes words.val v w) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), r.val.length = k.val.toNat ∧

        (∀ (j : Nat) (v : Word), j < r.val.length → r.val[j]? = some v →
          occursIn words.val v) ∧

        (∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
          r.val[i]? = some vi → r.val[j]? = some vj → vi.val ≠ vj.val) ∧

        (∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
          r.val[i]? = some vi → r.val[j]? = some vj → precedes words.val vi vj) ∧

        (∀ (v w : Word), occursIn words.val w → (∀ e ∈ r.val, e.val ≠ w.val) →
          r.val[r.val.length - 1]? = some v → precedes words.val v w)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_2
      (words : Slice Word) (k : I64)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int)) :
      ∃ r : alloc.vec.Vec Word, top_k_frequent words k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice Word) (k : I64)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int)), ∃ r : alloc.vec.Vec Word, top_k_frequent words k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = k (the natural number equal to the positive integer k).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_3
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      r.val.length = k.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), r.val.length = k.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), there exists an index i with 0 <= i < len(words) such that words[i] = r[j] (byte-wise equality).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_4
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (j : Nat) (v : Word), j < r.val.length → r.val[j]? = some v →
        occursIn words.val v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (j : Nat) (v : Word), j < r.val.length → r.val[j]? = some v →
          occursIn words.val v) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < j < len(r), r[i] != r[j] (byte-wise inequality).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_5
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
        r.val[i]? = some vi → r.val[j]? = some vj → vi.val ≠ vj.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
          r.val[i]? = some vi → r.val[j]? = some vj → vi.val ≠ vj.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < j < len(r), freq(r[i]) >= freq(r[j]).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_6
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
        r.val[i]? = some vi → r.val[j]? = some vj →
        freq words.val vi ≥ freq words.val vj := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
          r.val[i]? = some vi → r.val[j]? = some vj →
          freq words.val vi ≥ freq words.val vj) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < j < len(r), if freq(r[i]) = freq(r[j]) then lex(r[i], r[j]).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_7
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
        r.val[i]? = some vi → r.val[j]? = some vj →
        freq words.val vi = freq words.val vj → lexBytes vi.val vj.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (i j : Nat) (vi vj : Word), i < j → j < r.val.length →
          r.val[i]? = some vi → r.val[j]? = some vj →
          freq words.val vi = freq words.val vj → lexBytes vi.val vj.val) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and every word w that occurs in words and is not equal to any entry of r, r[j] precedes w.
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_8
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (j : Nat) (v w : Word), j < r.val.length → r.val[j]? = some v →
        occursIn words.val w → (∀ e ∈ r.val, e.val ≠ w.val) →
        precedes words.val v w := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (j : Nat) (v w : Word), j < r.val.length → r.val[j]? = some v →
          occursIn words.val w → (∀ e ∈ r.val, e.val ≠ w.val) →
          precedes words.val v w) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the number of distinct byte sequences v that occur in words and satisfy v precedes r[j] is exactly j.
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_9
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (j : Nat) (v : Word), j < r.val.length → r.val[j]? = some v →
        numPreceding words.val v.val = j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (j : Nat) (v : Word), j < r.val.length → r.val[j]? = some v →
          numPreceding words.val v.val = j) := by
    sorry

  /-- Whenever the function returns a result r, for every word w occurring in words and every word v occurring in words with freq(v) = freq(w) and lex(v, w), if w is equal to some entry of r, then v is equal to some entry of r.
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_10
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (w v : Word), occursIn words.val w → occursIn words.val v →
        freq words.val v = freq words.val w → lexBytes v.val w.val →
        (∃ e ∈ r.val, e.val = w.val) → (∃ e ∈ r.val, e.val = v.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (w v : Word), occursIn words.val w → occursIn words.val v →
          freq words.val v = freq words.val w → lexBytes v.val w.val →
          (∃ e ∈ r.val, e.val = w.val) → (∃ e ∈ r.val, e.val = v.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every word w occurring in words and every word v occurring in words with freq(v) > freq(w), if w is equal to some entry of r, then v is equal to some entry of r.
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_11
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (w v : Word), occursIn words.val w → occursIn words.val v →
        freq words.val v > freq words.val w →
        (∃ e ∈ r.val, e.val = w.val) → (∃ e ∈ r.val, e.val = v.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (w v : Word), occursIn words.val w → occursIn words.val v →
          freq words.val v > freq words.val w →
          (∃ e ∈ r.val, e.val = w.val) → (∃ e ∈ r.val, e.val = v.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and every word w that occurs in words and is not equal to any entry of r, freq(r[j]) >= freq(w).
    Preconditions: Let U be the number of distinct byte sequences occurring in words. len(words) is between 1 and 500 inclusive. For every i with 0 <= i < len(words), len(words[i]) is between 1 and 10 inclusive and every byte of words[i] is a lowercase ASCII letter (code 97..122). k is an integer with 1 <= k <= U. For a byte sequence w, freq(w) is the number of indices i with 0 <= i < len(words) and words[i] = w (byte-wise equality). For byte sequences x,y, lex(x,y) means x is lexicographically smaller than y: either x is a proper prefix of y (len(x) < len(y) and x[i]=y[i] for all 0 <= i < len(x)), or there is p with 0 <= p < min(len(x),len(y)), x[i]=y[i] for all 0 <= i < p, and x[p] < y[p]. A word v precedes a word w when freq(v) > freq(w), or freq(v)=freq(w) and lex(v,w). -/
  theorem spec_12
      (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
      (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
      (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
      (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
      (hr : top_k_frequent words k = ok r) :
      ∀ (j : Nat) (v w : Word), j < r.val.length → r.val[j]? = some v →
        occursIn words.val w → (∀ e ∈ r.val, e.val ≠ w.val) →
        freq words.val v ≥ freq words.val w := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice Word) (k : I64) (r : alloc.vec.Vec Word)
        (hn_pos : 1 ≤ words.val.length) (hn_le : words.val.length ≤ 500)
        (hw_len : ∀ u ∈ words.val, 1 ≤ u.val.length ∧ u.val.length ≤ 10)
        (hw_bytes : ∀ u ∈ words.val, ∀ b ∈ u.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (numDistinct words.val : Int))
        (hr : top_k_frequent words k = ok r), ∀ (j : Nat) (v w : Word), j < r.val.length → r.val[j]? = some v →
          occursIn words.val w → (∀ e ∈ r.val, e.val ≠ w.val) →
          freq words.val v ≥ freq words.val w) := by
    sorry

  end AegisSpec.TopKFrequent
