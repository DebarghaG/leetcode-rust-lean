import Aegis.PrefixCount.Code.Funs

/-!
# Specifications of `Aegis.PrefixCount.prefix_count`

LeetCode problem `counting-words-with-a-given-prefix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PrefixCount

def IsLowercaseByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def ByteArrayOk (l : List Std.U8) : Prop :=
  1 ≤ l.length ∧ l.length ≤ 100 ∧ ∀ b ∈ l, IsLowercaseByte b

def WordOk (w : alloc.vec.Vec Std.U8) : Prop := ByteArrayOk w.val

def WordsOk (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ words.val.length ∧ words.val.length ≤ 100 ∧
    ∀ (j : Nat) (h : j < words.val.length), WordOk (words.val.get ⟨j, h⟩)

def PrefOk (pref : Slice Std.U8) : Prop := ByteArrayOk pref.val

def IsPrefix (pref w : List Std.U8) : Prop :=
  pref.length ≤ w.length ∧ ∀ i : Nat, i < pref.length → w[i]? = pref[i]?

noncomputable def numPrefixed (pref : List Std.U8) (ws : List (alloc.vec.Vec Std.U8)) : Nat := by
  classical
  exact (ws.filter fun w => decide (IsPrefix pref w.val)).length

noncomputable def prefixIndicator (pref w : List Std.U8) : Int := by
  classical
  exact if IsPrefix pref w then 1 else 0

def numLongEnough (pref : List Std.U8) (ws : List (alloc.vec.Vec Std.U8)) : Nat :=
  (ws.filter fun w => decide (pref.length ≤ w.val.length)).length

def numSameFirstByte (pref : List Std.U8) (ws : List (alloc.vec.Vec Std.U8)) : Nat :=
  (ws.filter fun w => decide (w.val.head? = pref.head?)).length

def IsPermutation (W1 W2 : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∃ f : Fin W1.length ≃ Fin W2.length, ∀ j : Fin W1.length, W2.get (f j) = W1.get j

def IsDeletion (W1 W2 : List (alloc.vec.Vec Std.U8)) : Prop :=
  ∃ idx : Fin W2.length → Fin W1.length,
    StrictMono idx ∧ ∀ k : Fin W2.length, W1.get (idx k) = W2.get k

/-- The function returns a result r, and the integer value of r equals the number of indices j with 0 <= j < len(words) such that words[j] starts with pref, where a word w starts with pref iff len(pref) <= len(w) and for every i with 0 <= i < len(pref), w[i] = pref[i].
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val = (numPrefixed pref.val words.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val = (numPrefixed pref.val words.val : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result: it does not panic, overflow, fail an arithmetic check, or read outside the bounds of words, words[j], or pref.
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) :
    ∃ r : Std.I64, Aegis.PrefixCount.prefix_count words pref = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref), ∃ r : Std.I64, Aegis.PrefixCount.prefix_count words pref = ok r) := by
  sorry

/-- The function returns a result r, and 0 <= the integer value of r <= len(words).
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (words.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (words.val.length : Int)) := by
  sorry

/-- The function returns a result r, and the integer value of r > 0 if and only if there exists an index j with 0 <= j < len(words) such that len(pref) <= len(words[j]) and words[j][i] = pref[i] for every i with 0 <= i < len(pref).
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        (0 < r.val ↔
          ∃ (j : Nat) (h : j < words.val.length),
            IsPrefix pref.val (words.val.get ⟨j, h⟩).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        (0 < r.val ↔
          ∃ (j : Nat) (h : j < words.val.length),
            IsPrefix pref.val (words.val.get ⟨j, h⟩).val)) := by
  sorry

/-- The function returns a result r, and the integer value of r = len(words) if and only if for every j with 0 <= j < len(words), len(pref) <= len(words[j]) and words[j][i] = pref[i] for every i with 0 <= i < len(pref).
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        (r.val = (words.val.length : Int) ↔
          ∀ (j : Nat) (h : j < words.val.length),
            IsPrefix pref.val (words.val.get ⟨j, h⟩).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        (r.val = (words.val.length : Int) ↔
          ∀ (j : Nat) (h : j < words.val.length),
            IsPrefix pref.val (words.val.get ⟨j, h⟩).val)) := by
  sorry

/-- If len(words) = 1, then the function returns a result r, and the integer value of r = 1 if len(pref) <= len(words[0]) and words[0][i] = pref[i] for every i with 0 <= i < len(pref), and the integer value of r = 0 otherwise.
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) (hlen : words.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val = prefixIndicator pref.val (words.val.get ⟨0, by omega⟩).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) (hlen : words.val.length = 1), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val = prefixIndicator pref.val (words.val.get ⟨0, by omega⟩).val) := by
  sorry

/-- For every such p and q, if p is a prefix of q (len(p) <= len(q) and p[i] = q[i] for every i with 0 <= i < len(p)), then prefix_count(words,p) returns a result rp, prefix_count(words,q) returns a result rq, and the integer value of rq <= the integer value of rp.
  Preconditions: words satisfies the problem constraints: len(words) is between 1 and 100 inclusive, every words[j] has length between 1 and 100 inclusive and consists of lowercase English letters. Byte arrays p and q each have length between 1 and 100 inclusive and consist of lowercase English letters. -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (p q : Slice Std.U8)
    (hwords : WordsOk words) (hp : ByteArrayOk p.val) (hq : ByteArrayOk q.val)
    (hpref : IsPrefix p.val q.val) :
    ∃ rp rq : Std.I64,
      Aegis.PrefixCount.prefix_count words p = ok rp ∧
        Aegis.PrefixCount.prefix_count words q = ok rq ∧ rq.val ≤ rp.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (p q : Slice Std.U8)
    (hwords : WordsOk words) (hp : ByteArrayOk p.val) (hq : ByteArrayOk q.val)
    (hpref : IsPrefix p.val q.val), ∃ rp rq : Std.I64,
      Aegis.PrefixCount.prefix_count words p = ok rp ∧
        Aegis.PrefixCount.prefix_count words q = ok rq ∧ rq.val ≤ rp.val) := by
  sorry

/-- If W2 is a permutation of W1, meaning len(W2) = len(W1) and there is a bijection f from {0,...,len(W1)-1} to {0,...,len(W2)-1} such that W2[f(j)] is byte-for-byte equal to W1[j] for every j with 0 <= j < len(W1), then prefix_count(W1,pref) returns a result r1, prefix_count(W2,pref) returns a result r2, and the integer values of r1 and r2 are equal.
  Preconditions: Word lists W1 and W2 each satisfy the problem word-list constraints: their lengths are between 1 and 100 inclusive, and every W1[j] and W2[k] has length between 1 and 100 inclusive and consists of lowercase English letters. pref has length between 1 and 100 inclusive and consists of lowercase English letters. -/
theorem spec_8 (W1 W2 : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hW1 : WordsOk W1) (hW2 : WordsOk W2) (hpref : PrefOk pref)
    (hperm : IsPermutation W1.val W2.val) :
    ∃ r1 r2 : Std.I64,
      Aegis.PrefixCount.prefix_count W1 pref = ok r1 ∧
        Aegis.PrefixCount.prefix_count W2 pref = ok r2 ∧ r1.val = r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (W1 W2 : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hW1 : WordsOk W1) (hW2 : WordsOk W2) (hpref : PrefOk pref)
    (hperm : IsPermutation W1.val W2.val), ∃ r1 r2 : Std.I64,
      Aegis.PrefixCount.prefix_count W1 pref = ok r1 ∧
        Aegis.PrefixCount.prefix_count W2 pref = ok r2 ∧ r1.val = r2.val) := by
  sorry

/-- If len(W1) = len(W2) and for every j with 0 <= j < len(W1), W1[j] starts with pref exactly when W2[j] starts with pref (where a word w starts with pref iff len(pref) <= len(w) and w[i] = pref[i] for every i with 0 <= i < len(pref)), then prefix_count(W1,pref) returns a result r1, prefix_count(W2,pref) returns a result r2, and the integer values of r1 and r2 are equal.
  Preconditions: Word lists W1 and W2 each satisfy the problem word-list constraints: their lengths are between 1 and 100 inclusive, and every W1[j] and W2[k] has length between 1 and 100 inclusive and consists of lowercase English letters. pref has length between 1 and 100 inclusive and consists of lowercase English letters. -/
theorem spec_9 (W1 W2 : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hW1 : WordsOk W1) (hW2 : WordsOk W2) (hpref : PrefOk pref)
    (hlen : W1.val.length = W2.val.length)
    (hsame : ∀ (j : Nat) (h1 : j < W1.val.length) (h2 : j < W2.val.length),
      (IsPrefix pref.val (W1.val.get ⟨j, h1⟩).val ↔
        IsPrefix pref.val (W2.val.get ⟨j, h2⟩).val)) :
    ∃ r1 r2 : Std.I64,
      Aegis.PrefixCount.prefix_count W1 pref = ok r1 ∧
        Aegis.PrefixCount.prefix_count W2 pref = ok r2 ∧ r1.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (W1 W2 : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hW1 : WordsOk W1) (hW2 : WordsOk W2) (hpref : PrefOk pref)
    (hlen : W1.val.length = W2.val.length)
    (hsame : ∀ (j : Nat) (h1 : j < W1.val.length) (h2 : j < W2.val.length),
      (IsPrefix pref.val (W1.val.get ⟨j, h1⟩).val ↔
        IsPrefix pref.val (W2.val.get ⟨j, h2⟩).val)), ∃ r1 r2 : Std.I64,
      Aegis.PrefixCount.prefix_count W1 pref = ok r1 ∧
        Aegis.PrefixCount.prefix_count W2 pref = ok r2 ∧ r1.val = r2.val) := by
  sorry

/-- The function returns a result r, and the integer value of r <= the number of indices j with 0 <= j < len(words) for which len(words[j]) >= len(pref).
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val ≤ (numLongEnough pref.val words.val : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val ≤ (numLongEnough pref.val words.val : Int)) := by
  sorry

/-- If len(pref) = 1, then the function returns a result r, and the integer value of r equals the number of indices j with 0 <= j < len(words) such that words[j][0] = pref[0].
  Preconditions: len(words) is between 1 and 100 inclusive; for every j with 0 <= j < len(words), len(words[j]) is between 1 and 100 inclusive; len(pref) is between 1 and 100 inclusive; every byte of every words[j] and of pref is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_11 (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) (hlen : pref.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val = (numSameFirstByte pref.val words.val : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hwords : WordsOk words) (hpref : PrefOk pref) (hlen : pref.val.length = 1), ∃ r : Std.I64,
      Aegis.PrefixCount.prefix_count words pref = ok r ∧
        r.val = (numSameFirstByte pref.val words.val : Int)) := by
  sorry

/-- If W2 is obtained from W1 by deleting zero or more entries (equivalently, there are indices 0 <= i_0 < i_1 < ... < i_{len(W2)-1} < len(W1) such that W2[k] is byte-for-byte equal to W1[i_k] for every k with 0 <= k < len(W2)), then prefix_count(W1,pref) returns a result r1, prefix_count(W2,pref) returns a result r2, and the integer value of r2 <= the integer value of r1.
  Preconditions: Word lists W1 and W2 each satisfy the problem word-list constraints: their lengths are between 1 and 100 inclusive, and every word in either list has length between 1 and 100 inclusive and consists of lowercase English letters. pref has length between 1 and 100 inclusive and consists of lowercase English letters. -/
theorem spec_12 (W1 W2 : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hW1 : WordsOk W1) (hW2 : WordsOk W2) (hpref : PrefOk pref)
    (hdel : IsDeletion W1.val W2.val) :
    ∃ r1 r2 : Std.I64,
      Aegis.PrefixCount.prefix_count W1 pref = ok r1 ∧
        Aegis.PrefixCount.prefix_count W2 pref = ok r2 ∧ r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (W1 W2 : Slice (alloc.vec.Vec Std.U8)) (pref : Slice Std.U8)
    (hW1 : WordsOk W1) (hW2 : WordsOk W2) (hpref : PrefOk pref)
    (hdel : IsDeletion W1.val W2.val), ∃ r1 r2 : Std.I64,
      Aegis.PrefixCount.prefix_count W1 pref = ok r1 ∧
        Aegis.PrefixCount.prefix_count W2 pref = ok r2 ∧ r2.val ≤ r1.val) := by
  sorry

/-- Let b be 1 if len(pref) <= len(w) and w[i] = pref[i] for every i with 0 <= i < len(pref), and let b be 0 otherwise. Then prefix_count(W ++ [w], pref) returns a result r, prefix_count(W, pref) returns a result r0, and the integer value of r = the integer value of r0 + b.
  Preconditions: W is a word list with 1 <= len(W) <= 99, and every W[j] has length between 1 and 100 inclusive and consists of lowercase English letters. w is a byte array of length between 1 and 100 inclusive consisting of lowercase English letters. pref has length between 1 and 100 inclusive and consists of lowercase English letters. Consequently W ++ [w] also satisfies the problem word-list constraints. -/
theorem spec_13 (W : Slice (alloc.vec.Vec Std.U8)) (w : alloc.vec.Vec Std.U8)
    (pref : Slice Std.U8) (hW : WordsOk W) (hw : WordOk w) (hWlen : W.val.length ≤ 99)
    (hpref : PrefOk pref) :
    ∀ Wnew : Slice (alloc.vec.Vec Std.U8), Wnew.val = W.val ++ [w] →
      ∃ r r0 : Std.I64,
        Aegis.PrefixCount.prefix_count Wnew pref = ok r ∧
          Aegis.PrefixCount.prefix_count W pref = ok r0 ∧
            r.val = r0.val + prefixIndicator pref.val w.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (W : Slice (alloc.vec.Vec Std.U8)) (w : alloc.vec.Vec Std.U8)
    (pref : Slice Std.U8) (hW : WordsOk W) (hw : WordOk w) (hWlen : W.val.length ≤ 99)
    (hpref : PrefOk pref), ∀ Wnew : Slice (alloc.vec.Vec Std.U8), Wnew.val = W.val ++ [w] →
      ∃ r r0 : Std.I64,
        Aegis.PrefixCount.prefix_count Wnew pref = ok r ∧
          Aegis.PrefixCount.prefix_count W pref = ok r0 ∧
            r.val = r0.val + prefixIndicator pref.val w.val) := by
  sorry

end AegisSpec.PrefixCount
