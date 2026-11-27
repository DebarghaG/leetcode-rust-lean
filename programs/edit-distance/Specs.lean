import Aegis.MinDistance.Code.Funs

/-!
# Specifications of `Aegis.MinDistance.min_distance`

LeetCode problem `edit-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinDistance

  def IsLowercaseByte (b : Aeneas.Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def AllLowercase (s : List Aeneas.Std.U8) : Prop := ∀ b ∈ s, IsLowercaseByte b

  inductive Aligns : List Aeneas.Std.U8 → List Aeneas.Std.U8 → ℕ → Prop where
    | nil : Aligns [] [] 0
    | matchEq {x : Aeneas.Std.U8} {xs ys : List Aeneas.Std.U8} {c : ℕ} :
        Aligns xs ys c → Aligns (x :: xs) (x :: ys) c
    | subst {x y : Aeneas.Std.U8} {xs ys : List Aeneas.Std.U8} {c : ℕ} :
        x ≠ y → Aligns xs ys c → Aligns (x :: xs) (y :: ys) (c + 1)
    | delete {x : Aeneas.Std.U8} {xs ys : List Aeneas.Std.U8} {c : ℕ} :
        Aligns xs ys c → Aligns (x :: xs) ys (c + 1)
    | insert {y : Aeneas.Std.U8} {xs ys : List Aeneas.Std.U8} {c : ℕ} :
        Aligns xs ys c → Aligns xs (y :: ys) (c + 1)

  noncomputable def editDist (a b : List Aeneas.Std.U8) : ℕ := sInf {c : ℕ | Aligns a b c}

  lemma aligns_delete_all (a : List Aeneas.Std.U8) : Aligns a [] a.length := by
    induction a with
    | nil => exact Aligns.nil
    | cons x xs ih => exact Aligns.delete ih

  lemma aligns_delete_then_insert (a b : List Aeneas.Std.U8) :
      Aligns a b (a.length + b.length) := by
    induction b with
    | nil => exact aligns_delete_all a
    | cons y ys ih => exact Aligns.insert ih

  lemma exists_aligns_editDist (a b : List Aeneas.Std.U8) : Aligns a b (editDist a b) :=
    Set.mem_ofPred.mp (Nat.sInf_mem ⟨_, aligns_delete_then_insert a b⟩)

  lemma editDist_le {a b : List Aeneas.Std.U8} {c : ℕ} (h : Aligns a b c) :
      editDist a b ≤ c :=
    Nat.sInf_le (s := {c : ℕ | Aligns a b c}) (Set.mem_ofPred.mpr h)

  def mismatchCount (a b : List Aeneas.Std.U8) : ℕ :=
    (List.zipWith (fun x y => if x = y then 0 else 1) a b).sum

  def IsCommonSubsequence (s a b : List Aeneas.Std.U8) : Prop :=
    s.Sublist a ∧ s.Sublist b

  def lcsLen (a b : List Aeneas.Std.U8) : ℕ :=
    ((a.sublists.filter (fun s => decide (s.Sublist b))).map List.length).foldr max 0

  def IsInsertion (a b : List Aeneas.Std.U8) : Prop :=
    ∃ (x y : List Aeneas.Std.U8) (c : Aeneas.Std.U8), a = x ++ y ∧ b = x ++ c :: y

  def IsDeletion (a b : List Aeneas.Std.U8) : Prop :=
    ∃ (x y : List Aeneas.Std.U8) (c : Aeneas.Std.U8), a = x ++ c :: y ∧ b = x ++ y

  def IsSubstitution (a b : List Aeneas.Std.U8) : Prop :=
    ∃ (x y : List Aeneas.Std.U8) (c d : Aeneas.Std.U8),
      c ≠ d ∧ a = x ++ c :: y ∧ b = x ++ d :: y

  /-- The function returns a result r (an i64) such that r equals the edit distance d(word1, word2). The edit distance d(a, b) between two byte sequences a and b is defined as the minimum total cost over all edit alignments between a and b. An edit alignment is a sequence of steps that consumes all characters of a and b in order; each step is one of: (match) consume a character a[i] and a character b[j] with a[i] = b[j], cost 0; (substitute) consume a character a[i] and a character b[j] with a[i] ≠ b[j], cost 1; (delete) consume a character a[i], cost 1; (insert) consume a character b[j], cost 1. The indices of consumed characters in a are strictly increasing, as are the indices in b. The cost of an alignment is the sum of its step costs. Then d(a, b) is the minimum cost over all such alignments. Equivalently, d(a, b) is the minimum number of single-character insertions, deletions, and replacements required to transform a into b.
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_1 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val) :
      ∃ r : Aeneas.Std.I64, Aegis.MinDistance.min_distance word1 word2 = ok r ∧
        r.val = (editDist word1.val word2.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val), ∃ r : Aeneas.Std.I64, Aegis.MinDistance.min_distance word1 word2 = ok r ∧
          r.val = (editDist word1.val word2.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ |len(word1) - len(word2)|, where len(x) denotes the number of bytes in x.
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_2 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      |(word1.len.val : ℤ) - (word2.len.val : ℤ)| ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), |(word1.len.val : ℤ) - (word2.len.val : ℤ)| ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r ≤ max(len(word1), len(word2)).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_3 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      r.val ≤ (max word1.len.val word2.len.val : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), r.val ≤ (max word1.len.val word2.len.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if len(word1) = 0 then r = len(word2).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_4 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
      (h0 : word1.len.val = 0) :
      r.val = (word2.len.val : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
        (h0 : word1.len.val = 0), r.val = (word2.len.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if len(word2) = 0 then r = len(word1).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_5 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
      (h0 : word2.len.val = 0) :
      r.val = (word1.len.val : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
        (h0 : word2.len.val = 0), r.val = (word1.len.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if word1 and word2 are byte-wise equal (len(word1) = len(word2) and word1[i] = word2[i] for all 0 ≤ i < len(word1)).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_6 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      (r.val = 0 ↔ word1.val = word2.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), (r.val = 0 ↔ word1.val = word2.val)) := by
    sorry

  /-- Whenever the function returns a result r for (word1, word2), r is also the edit distance from word2 to word1, i.e., the minimum number of single-character insertions, deletions, and replacements required to transform word2 into word1.
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_7 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      r.val = (editDist word2.val word1.val : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), r.val = (editDist word2.val word1.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r for (word1, word2), for every byte sequence x, the edit distance d(x concatenated with word1, x concatenated with word2) equals r (where d is the edit distance defined in the main specification).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_8 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      ∀ x : List Aeneas.Std.U8,
        (editDist (x ++ word1.val) (x ++ word2.val) : ℤ) = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), ∀ x : List Aeneas.Std.U8,
          (editDist (x ++ word1.val) (x ++ word2.val) : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r for (word1, word2), for every byte sequence x, the edit distance d(word1 concatenated with x, word2 concatenated with x) equals r (where d is the edit distance defined in the main specification).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_9 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      ∀ x : List Aeneas.Std.U8,
        (editDist (word1.val ++ x) (word2.val ++ x) : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), ∀ x : List Aeneas.Std.U8,
          (editDist (word1.val ++ x) (word2.val ++ x) : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r for (word1, word2), for every byte sequence w, r ≤ d(word1, w) + d(w, word2), where d is the edit distance. In other words, the edit distance satisfies the triangle inequality: d(word1, word2) ≤ d(word1, w) + d(w, word2).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_10 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      ∀ w : List Aeneas.Std.U8,
        r.val ≤ (editDist word1.val w : ℤ) + (editDist w word2.val : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), ∀ w : List Aeneas.Std.U8,
          r.val ≤ (editDist word1.val w : ℤ) + (editDist w word2.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if len(word1) = len(word2) = n, then r ≤ H, where H is the number of indices i with 0 ≤ i < n and word1[i] ≠ word2[i].
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_11 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
      (hlen : word1.len.val = word2.len.val) :
      r.val ≤ (mismatchCount word1.val word2.val : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
        (hlen : word1.len.val = word2.len.val), r.val ≤ (mismatchCount word1.val word2.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let L be the length of a longest common subsequence of word1 and word2 (i.e., the maximum length of a byte sequence that is a subsequence of both word1 and word2). Then max(len(word1), len(word2)) - L ≤ r ≤ len(word1) + len(word2) - 2L.
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_12 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      (max word1.len.val word2.len.val : ℤ) - (lcsLen word1.val word2.val : ℤ) ≤ r.val ∧
        r.val ≤ (word1.len.val : ℤ) + (word2.len.val : ℤ) -
          2 * (lcsLen word1.val word2.val : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), (max word1.len.val word2.len.val : ℤ) - (lcsLen word1.val word2.val : ℤ) ≤ r.val ∧
          r.val ≤ (word1.len.val : ℤ) + (word2.len.val : ℤ) -
            2 * (lcsLen word1.val word2.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if word1 is a prefix of word2 (i.e., there exists a byte sequence x such that word2 = word1 concatenated with x), then r = len(word2) - len(word1).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_13 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
      (hpre : ∃ x : List Aeneas.Std.U8, word2.val = word1.val ++ x) :
      r.val = (word2.len.val : ℤ) - (word1.len.val : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
        (hpre : ∃ x : List Aeneas.Std.U8, word2.val = word1.val ++ x), r.val = (word2.len.val : ℤ) - (word1.len.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if word1 is a suffix of word2 (i.e., there exists a byte sequence x such that word2 = x concatenated with word1), then r = len(word2) - len(word1).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_14 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
      (hsuf : ∃ x : List Aeneas.Std.U8, word2.val = x ++ word1.val) :
      r.val = (word2.len.val : ℤ) - (word1.len.val : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r)
        (hsuf : ∃ x : List Aeneas.Std.U8, word2.val = x ++ word1.val), r.val = (word2.len.val : ℤ) - (word1.len.val : ℤ)) := by
    sorry

  /-- For every word1 and word2 satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_15 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val) :
      ∃ r : Aeneas.Std.I64, Aegis.MinDistance.min_distance word1 word2 = ok r := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val), ∃ r : Aeneas.Std.I64, Aegis.MinDistance.min_distance word1 word2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if word1 ≠ word2 and at least one of the following holds: (i) there exist byte sequences x, y and a byte c such that word1 = x concatenated with y and word2 = x concatenated with c concatenated with y (i.e., word2 is obtained by inserting one byte into word1); (ii) there exist byte sequences x, y and a byte c such that word1 = x concatenated with c concatenated with y and word2 = x concatenated with y (i.e., word2 is obtained by deleting one byte from word1); (iii) there exist byte sequences x, y and bytes c ≠ d such that word1 = x concatenated with c concatenated with y and word2 = x concatenated with d concatenated with y (i.e., word2 is obtained by replacing one byte of word1 with a different byte).
    Preconditions: 0 ≤ len(word1) ≤ 500, 0 ≤ len(word2) ≤ 500, and every byte of word1 and word2 is a lowercase English letter (97 ≤ byte ≤ 122). -/
  theorem spec_16 (word1 word2 : Slice Aeneas.Std.U8)
      (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
      (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
      (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r) :
      (r.val = 1 ↔ word1.val ≠ word2.val ∧
        (IsInsertion word1.val word2.val ∨ IsDeletion word1.val word2.val ∨
          IsSubstitution word1.val word2.val)) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (word1 word2 : Slice Aeneas.Std.U8)
        (h1len : word1.len.val ≤ 500) (h2len : word2.len.val ≤ 500)
        (h1lc : AllLowercase word1.val) (h2lc : AllLowercase word2.val)
        (r : Aeneas.Std.I64) (hr : Aegis.MinDistance.min_distance word1 word2 = ok r), (r.val = 1 ↔ word1.val ≠ word2.val ∧
          (IsInsertion word1.val word2.val ∨ IsDeletion word1.val word2.val ∨
            IsSubstitution word1.val word2.val))) := by
    sorry

  end AegisSpec.MinDistance
