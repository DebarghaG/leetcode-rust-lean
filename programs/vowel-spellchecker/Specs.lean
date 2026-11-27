import Aegis.Spellchecker.Code.Funs

/-!
# Specifications of `Aegis.Spellchecker.spellchecker`

LeetCode problem `vowel-spellchecker`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Spellchecker

abbrev Byte := U8

def IsAsciiLetter (c : Nat) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)

def lowerByte (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

def bytes (w : List Byte) : List Nat := w.map (fun c => c.val)

def lower (w : List Byte) : List Nat := (bytes w).map lowerByte

def IsVowel (c : Nat) : Prop := c = 97 ∨ c = 101 ∨ c = 105 ∨ c = 111 ∨ c = 117

instance instDecidableIsVowel (c : Nat) : Decidable (IsVowel c) := by
  unfold IsVowel
  infer_instance

def vnByte (c : Nat) : Nat := if IsVowel (lowerByte c) then 0 else lowerByte c

def vn (w : List Byte) : List Nat := (bytes w).map vnByte

def word? (ws : List (alloc.vec.Vec Byte)) (j : Nat) : Option (List Byte) :=
  (ws[j]?).map (fun w => w.val)

def answer? (r : alloc.vec.Vec (alloc.vec.Vec Byte)) (i : Nat) : Option (List Byte) :=
  (r.val[i]?).map (fun w => w.val)

def AnswerEmpty (r : alloc.vec.Vec (alloc.vec.Vec Byte)) (i : Nat) : Prop :=
  answer? r i = some []

def AnswerIsWord (r : alloc.vec.Vec (alloc.vec.Vec Byte)) (ws : List (alloc.vec.Vec Byte))
    (i j : Nat) : Prop :=
  ∃ w, word? ws j = some w ∧ answer? r i = some w

def IsLeastMatch (p : List Byte → Prop) (ws : List (alloc.vec.Vec Byte)) (j : Nat) : Prop :=
  ∃ w, word? ws j = some w ∧ p w ∧ ∀ k, k < j → ∀ v, word? ws k = some v → ¬ p v

def HasExact (ws : List (alloc.vec.Vec Byte)) (q : List Byte) : Prop :=
  ∃ w ∈ ws, w.val = q

def HasLower (ws : List (alloc.vec.Vec Byte)) (q : List Byte) : Prop :=
  ∃ w ∈ ws, lower w.val = lower q

def HasVowel (ws : List (alloc.vec.Vec Byte)) (q : List Byte) : Prop :=
  ∃ w ∈ ws, vn w.val = vn q

/-- Write lower(w) for the byte vector obtained from w by replacing every byte c with 65 <= c <= 90 by c+32 and leaving every other byte unchanged. Write vn(w) for the byte vector of the same length with vn(w)[p] = 0 if lower(w)[p] is one of 97,101,105,111,117 (the lowercase vowels a,e,i,o,u), and vn(w)[p] = lower(w)[p] otherwise. Byte-vector equality is exact string equality; [] is the empty byte vector. The function returns a result r, len(r)=len(queries), and for every i with 0 <= i < len(queries), writing q=queries[i], r[i] is determined by the following precedence: (1) if there exists j with wordlist[j]=q, then r[i]=q; (2) otherwise, if there exists j with lower(wordlist[j])=lower(q), then r[i]=wordlist[j0] where j0 is the least such j; (3) otherwise, if there exists j with vn(wordlist[j])=vn(q), then r[i]=wordlist[j0] where j0 is the least such j; (4) otherwise r[i]=[].
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_1 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ i (hi : i < queries.val.length),
        (HasExact wordlist.val (queries.val[i]).val ∧
          answer? r i = some (queries.val[i]).val) ∨
        (¬ HasExact wordlist.val (queries.val[i]).val ∧
          ∃ j, IsLeastMatch (fun w => lower w = lower (queries.val[i]).val) wordlist.val j ∧
            AnswerIsWord r wordlist.val i j) ∨
        (¬ HasExact wordlist.val (queries.val[i]).val ∧
          ¬ HasLower wordlist.val (queries.val[i]).val ∧
          ∃ j, IsLeastMatch (fun w => vn w = vn (queries.val[i]).val) wordlist.val j ∧
            AnswerIsWord r wordlist.val i j) ∨
        (¬ HasExact wordlist.val (queries.val[i]).val ∧
          ¬ HasLower wordlist.val (queries.val[i]).val ∧
          ¬ HasVowel wordlist.val (queries.val[i]).val ∧
          AnswerEmpty r i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ i (hi : i < queries.val.length),
        (HasExact wordlist.val (queries.val[i]).val ∧
          answer? r i = some (queries.val[i]).val) ∨
        (¬ HasExact wordlist.val (queries.val[i]).val ∧
          ∃ j, IsLeastMatch (fun w => lower w = lower (queries.val[i]).val) wordlist.val j ∧
            AnswerIsWord r wordlist.val i j) ∨
        (¬ HasExact wordlist.val (queries.val[i]).val ∧
          ¬ HasLower wordlist.val (queries.val[i]).val ∧
          ∃ j, IsLeastMatch (fun w => vn w = vn (queries.val[i]).val) wordlist.val j ∧
            AnswerIsWord r wordlist.val i j) ∨
        (¬ HasExact wordlist.val (queries.val[i]).val ∧
          ¬ HasLower wordlist.val (queries.val[i]).val ∧
          ¬ HasVowel wordlist.val (queries.val[i]).val ∧
          AnswerEmpty r i)) := by
  sorry

/-- The function returns a result r and len(r)=len(queries); equivalently, there is exactly one answer entry for each query index i with 0 <= i < len(queries).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_2 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ i (hi : i < queries.val.length), ∃ out, answer? r i = some out := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ i (hi : i < queries.val.length), ∃ out, answer? r i = some out) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not overflow, panic, or otherwise fail.
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_3 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(queries), if there exists j with wordlist[j]=queries[i] (byte equality), then r[i]=queries[i]. This holds regardless of any earlier wordlist entry that is case-insensitive equal or vowel-equivalent to queries[i].
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_4 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        HasExact wordlist.val (queries.val[i]).val → answer? r i = some (queries.val[i]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        HasExact wordlist.val (queries.val[i]).val → answer? r i = some (queries.val[i]).val) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter. The function returns a result r and for every i with 0 <= i < len(queries), if no j has wordlist[j]=queries[i] and there exists j with lower(wordlist[j])=lower(queries[i]), then r[i]=wordlist[j0] where j0 is the least index j satisfying lower(wordlist[j])=lower(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_5 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        ¬ HasExact wordlist.val (queries.val[i]).val →
        HasLower wordlist.val (queries.val[i]).val →
        ∃ j, IsLeastMatch (fun w => lower w = lower (queries.val[i]).val) wordlist.val j ∧
          AnswerIsWord r wordlist.val i j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        ¬ HasExact wordlist.val (queries.val[i]).val →
        HasLower wordlist.val (queries.val[i]).val →
        ∃ j, IsLeastMatch (fun w => lower w = lower (queries.val[i]).val) wordlist.val j ∧
          AnswerIsWord r wordlist.val i j) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter, and vn(w) for the byte vector with vn(w)[p]=0 if lower(w)[p] is one of 97,101,105,111,117 (a,e,i,o,u), and vn(w)[p]=lower(w)[p] otherwise. The function returns a result r and for every i with 0 <= i < len(queries), if there is no j with wordlist[j]=queries[i] and no j with lower(wordlist[j])=lower(queries[i]), and there exists j with vn(wordlist[j])=vn(queries[i]), then r[i]=wordlist[j0] where j0 is the least index j satisfying vn(wordlist[j])=vn(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_6 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        ¬ HasExact wordlist.val (queries.val[i]).val →
        ¬ HasLower wordlist.val (queries.val[i]).val →
        HasVowel wordlist.val (queries.val[i]).val →
        ∃ j, IsLeastMatch (fun w => vn w = vn (queries.val[i]).val) wordlist.val j ∧
          AnswerIsWord r wordlist.val i j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        ¬ HasExact wordlist.val (queries.val[i]).val →
        ¬ HasLower wordlist.val (queries.val[i]).val →
        HasVowel wordlist.val (queries.val[i]).val →
        ∃ j, IsLeastMatch (fun w => vn w = vn (queries.val[i]).val) wordlist.val j ∧
          AnswerIsWord r wordlist.val i j) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter, and vn(w) for the byte vector with vn(w)[p]=0 if lower(w)[p] is one of 97,101,105,111,117 (a,e,i,o,u), and vn(w)[p]=lower(w)[p] otherwise. The function returns a result r and for every i with 0 <= i < len(queries), r[i]=[] if and only if there is no j with wordlist[j]=queries[i] and no j with lower(wordlist[j])=lower(queries[i]) and no j with vn(wordlist[j])=vn(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_7 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        (AnswerEmpty r i ↔
          (¬ HasExact wordlist.val (queries.val[i]).val ∧
            ¬ HasLower wordlist.val (queries.val[i]).val ∧
            ¬ HasVowel wordlist.val (queries.val[i]).val)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        (AnswerEmpty r i ↔
          (¬ HasExact wordlist.val (queries.val[i]).val ∧
            ¬ HasLower wordlist.val (queries.val[i]).val ∧
            ¬ HasVowel wordlist.val (queries.val[i]).val))) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(queries), if r[i] is nonempty then there exists j with wordlist[j]=r[i] (byte-for-byte, with the original capitalization of that wordlist entry).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_8 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out ≠ [] → ∃ w ∈ wordlist.val, w.val = out := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out ≠ [] → ∃ w ∈ wordlist.val, w.val = out) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(queries), either r[i]=[] or len(r[i])=len(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_9 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out = [] ∨ out.length = (queries.val[i]).val.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out = [] ∨ out.length = (queries.val[i]).val.length) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter, and vn(w) for the byte vector with vn(w)[p]=0 if lower(w)[p] is one of 97,101,105,111,117 (a,e,i,o,u), and vn(w)[p]=lower(w)[p] otherwise. The function returns a result r and for every i with 0 <= i < len(queries), if r[i] is nonempty then vn(r[i])=vn(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_10 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out ≠ [] → vn out = vn (queries.val[i]).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out ≠ [] → vn out = vn (queries.val[i]).val) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(queries), r[i]=queries[i] if and only if there exists j with wordlist[j]=queries[i] (byte equality).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_11 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        (answer? r i = some (queries.val[i]).val ↔ HasExact wordlist.val (queries.val[i]).val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length),
        (answer? r i = some (queries.val[i]).val ↔ HasExact wordlist.val (queries.val[i]).val)) := by
  sorry

/-- The function returns a result r and for every i,j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i]=queries[j] (byte equality), then r[i]=r[j].
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_12 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) j (hj : j < queries.val.length),
        (queries.val[i]).val = (queries.val[j]).val → answer? r i = answer? r j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) j (hj : j < queries.val.length),
        (queries.val[i]).val = (queries.val[j]).val → answer? r i = answer? r j) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter. The function returns a result r and for every i with 0 <= i < len(queries), if r[i] is nonempty and lower(r[i]) != lower(queries[i]), then there is no j with wordlist[j]=queries[i] and no j with lower(wordlist[j])=lower(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_13 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out ≠ [] → lower out ≠ lower (queries.val[i]).val →
        ¬ HasExact wordlist.val (queries.val[i]).val ∧
          ¬ HasLower wordlist.val (queries.val[i]).val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        answer? r i = some out → out ≠ [] → lower out ≠ lower (queries.val[i]).val →
        ¬ HasExact wordlist.val (queries.val[i]).val ∧
          ¬ HasLower wordlist.val (queries.val[i]).val) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter, and vn(w) for the byte vector with vn(w)[p]=0 if lower(w)[p] is one of 97,101,105,111,117 (a,e,i,o,u), and vn(w)[p]=lower(w)[p] otherwise. The function returns a result r and for every i with 0 <= i < len(queries), r[i]=wordlist[0] if vn(wordlist[0])=vn(queries[i]), and r[i]=[] otherwise.
  Preconditions: len(wordlist)=1 and len(queries) >= 1 and len(queries) <= 5000; wordlist[0] and every queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_14 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn1 : wordlist.val.length = 1) (hqn : 1 ≤ queries.val.length)
    (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (w0 : List Byte),
        word? wordlist.val 0 = some w0 →
          ((vn w0 = vn (queries.val[i]).val → answer? r i = some w0) ∧
            (vn w0 ≠ vn (queries.val[i]).val → AnswerEmpty r i)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn1 : wordlist.val.length = 1) (hqn : 1 ≤ queries.val.length)
    (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (w0 : List Byte),
        word? wordlist.val 0 = some w0 →
          ((vn w0 = vn (queries.val[i]).val → answer? r i = some w0) ∧
            (vn w0 ≠ vn (queries.val[i]).val → AnswerEmpty r i))) := by
  sorry

/-- Write lower(w) for the byte vector obtained from w by lowercasing each ASCII letter. The function returns a result r and for every i with 0 <= i < len(queries), if queries[i] contains no byte whose lowercase form is one of 97,101,105,111,117 (a,e,i,o,u), and r[i] is nonempty, then lower(r[i])=lower(queries[i]).
  Preconditions: len(wordlist) >= 1 and len(queries) >= 1 and len(wordlist) <= 5000 and len(queries) <= 5000; each wordlist[j] and queries[i] is a nonempty byte vector of length at most 7 whose bytes are ASCII letters (65-90 or 97-122). -/
theorem spec_15 (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val) :
    ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        (∀ c ∈ (queries.val[i]).val, ¬ IsVowel (lowerByte c.val)) →
        answer? r i = some out → out ≠ [] → lower out = lower (queries.val[i]).val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (wordlist queries : Slice (alloc.vec.Vec Byte))
    (hwn : 1 ≤ wordlist.val.length) (hqn : 1 ≤ queries.val.length)
    (hwn_le : wordlist.val.length ≤ 5000) (hqn_le : queries.val.length ≤ 5000)
    (hwwf : ∀ w ∈ wordlist.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val)
    (hqwf : ∀ w ∈ queries.val, 1 ≤ w.val.length ∧ w.val.length ≤ 7 ∧
      ∀ c ∈ w.val, IsAsciiLetter c.val), ∃ r, Aegis.Spellchecker.spellchecker wordlist queries = ok r ∧
      ∀ i (hi : i < queries.val.length) (out : List Byte),
        (∀ c ∈ (queries.val[i]).val, ¬ IsVowel (lowerByte c.val)) →
        answer? r i = some out → out ≠ [] → lower out = lower (queries.val[i]).val) := by
  sorry

end AegisSpec.Spellchecker
