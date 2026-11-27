import Aegis.LongestCommonPrefix.Code.Funs

/-!
# Specifications of `Aegis.LongestCommonPrefix.longest_common_prefix`

LeetCode problem `longest-common-prefix-of-k-strings-after-removal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestCommonPrefix

  def wordAt (words : Slice (alloc.vec.Vec Std.U8)) (j : ℕ) : alloc.vec.Vec Std.U8 :=
    words.val.getD j (alloc.vec.Vec.new Std.U8)

  def resAt (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := (r.val.getD i default).val

  def byteAt (w : alloc.vec.Vec Std.U8) (p : ℕ) : ℕ := (w.val.getD p default).val

  def totalLen (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
    (words.val.map fun w => w.val.length).sum

  def LowercaseWords (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ w ∈ words.val, w.val ≠ [] ∧ ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122

  def Pre (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) : Prop :=
    LowercaseWords words ∧
      totalLen words ≤ 100000 ∧
      1 ≤ words.val.length ∧
      1 ≤ k.val ∧ k.val ≤ (words.val.length : ℤ)

  def kNat (k : Std.I64) : ℕ := k.val.toNat

  def selWords (words : Slice (alloc.vec.Vec Std.U8)) (I : Finset ℕ) :
      List (alloc.vec.Vec Std.U8) :=
    (List.range words.val.length).filterMap fun j =>
      if j ∈ I then some (wordAt words j) else none

  def IsCommonPrefixLen (S : List (alloc.vec.Vec Std.U8)) (L : ℕ) : Prop :=
    ∀ p : ℕ, p < L →
      (∀ s ∈ S, p < s.val.length) ∧ (∀ s ∈ S, ∀ t ∈ S, byteAt s p = byteAt t p)

  noncomputable def cpLen (S : List (alloc.vec.Vec Std.U8)) : ℕ :=
    sSup { L : ℕ | IsCommonPrefixLen S L }

  theorem cpLen_le_length {S : List (alloc.vec.Vec Std.U8)} {w : alloc.vec.Vec Std.U8}
      (hw : w ∈ S) : cpLen S ≤ w.val.length := by
    classical
    unfold cpLen
    apply csSup_le ⟨0, by intro p hp; exact absurd hp (Nat.not_lt_zero p)⟩
    intro b hb
    by_contra hcon
    have hp : w.val.length < b := Nat.lt_of_not_le hcon
    exact absurd ((hb _ hp).1 w hw) (lt_irrefl _)

  theorem isCommonPrefixLen_cpLen {S : List (alloc.vec.Vec Std.U8)}
      {w : alloc.vec.Vec Std.U8} (hw : w ∈ S) : IsCommonPrefixLen S (cpLen S) := by
    classical
    have hs : sSup { L : ℕ | IsCommonPrefixLen S L } ∈ { L : ℕ | IsCommonPrefixLen S L } :=
      Nat.sSup_mem (s := { L : ℕ | IsCommonPrefixLen S L })
        ⟨0, by intro p hp; exact absurd hp (Nat.not_lt_zero p)⟩
        ⟨w.val.length, by
          intro b hb
          by_contra hcon
          have hp : w.val.length < b := Nat.lt_of_not_le hcon
          exact absurd ((hb _ hp).1 w hw) (lt_irrefl _)⟩
    exact hs

  theorem le_cpLen {S : List (alloc.vec.Vec Std.U8)} {w : alloc.vec.Vec Std.U8}
      (hw : w ∈ S) {L : ℕ} (hL : IsCommonPrefixLen S L) : L ≤ cpLen S := by
    classical
    unfold cpLen
    refine le_csSup ⟨w.val.length, ?_⟩ hL
    intro b hb
    by_contra hcon
    have hp : w.val.length < b := Nat.lt_of_not_le hcon
    exact absurd ((hb _ hp).1 w hw) (lt_irrefl _)

  def maxLen (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
    (Finset.range words.val.length).sup fun j => (wordAt words j).val.length

  def maxLenExcept (words : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : ℕ :=
    ((Finset.range words.val.length).erase i).sup fun j => (wordAt words j).val.length

  def IsMaxCPLen (words : Slice (alloc.vec.Vec Std.U8)) (i kk : ℕ) (v : ℤ) : Prop :=
    (∀ I : Finset ℕ, I ⊆ Finset.range words.val.length → i ∉ I → I.card = kk →
        (cpLen (selWords words I) : ℤ) ≤ v) ∧
      ∃ I : Finset ℕ, I ⊆ Finset.range words.val.length ∧ i ∉ I ∧ I.card = kk ∧
        (cpLen (selWords words I) : ℤ) = v

  /-- Let n = len(words). Whenever the function returns a result r, len(r) = n and for every i with 0 <= i < n the following holds. If n - 1 < k, then r[i] = 0. If n - 1 >= k, then r[i] is the maximum, over all subsets I of {0, 1, ..., n-1} such that i is not in I and |I| = k, of the common prefix length of the strings {words[j] : j in I}, where the common prefix length of a nonempty finite set S of byte strings is the largest L >= 0 such that for every p with 0 <= p < L and every s in S, p < len(s), and for all s, t in S, s[p] = t[p].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters (each byte is an ASCII code) with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          r.val.length = words.val.length ∧
            ∀ (i : ℕ), i < words.val.length →
              ((words.val.length : ℤ) - 1 < k.val → resAt r i = 0) ∧
                (k.val ≤ (words.val.length : ℤ) - 1 →
                  IsMaxCPLen words i (kNat k) (resAt r i)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            r.val.length = words.val.length ∧
              ∀ (i : ℕ), i < words.val.length →
                ((words.val.length : ℤ) - 1 < k.val → resAt r i = 0) ∧
                  (k.val ≤ (words.val.length : ℤ) - 1 →
                    IsMaxCPLen words i (kNat k) (resAt r i))) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(words).
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          r.val.length = words.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            r.val.length = words.val.length) := by
    sorry

  /-- Let M = max{len(words[j]) : 0 <= j < len(words)}. Whenever the function returns a result r, for every i with 0 <= i < len(words), 0 <= r[i] <= M.
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i : ℕ), i < words.val.length → 0 ≤ resAt r i ∧ resAt r i ≤ (maxLen words : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i : ℕ), i < words.val.length → 0 ≤ resAt r i ∧ resAt r i ≤ (maxLen words : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(words), r[i] = 0.
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words) and len(words) = k. -/
  theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
      (hk : k.val = (words.val.length : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i : ℕ), i < words.val.length → resAt r i = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
        (hk : k.val = (words.val.length : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i : ℕ), i < words.val.length → resAt r i = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(words), r[i] = max{len(words[j]) : 0 <= j < len(words) and j != i}, where the maximum over an empty set is defined to be 0.
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k = 1. -/
  theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
      (hk : k.val = 1) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i : ℕ), i < words.val.length → resAt r i = (maxLenExcept words i : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
        (hk : k.val = 1), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i : ℕ), i < words.val.length → resAt r i = (maxLenExcept words i : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(words), r[i] is the common prefix length of the set {words[j] : 0 <= j < len(words) and j != i}, i.e. the largest L >= 0 such that for every p with 0 <= p < L and all j, j' with 0 <= j < len(words), 0 <= j' < len(words), j != i, and j' != i, we have p < len(words[j]) and words[j][p] = words[j'][p].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 2 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k = len(words) - 1. -/
  theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
      (hn : 2 ≤ words.val.length) (hk : k.val = (words.val.length : ℤ) - 1) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i : ℕ), i < words.val.length →
            resAt r i =
              (cpLen (selWords words ((Finset.range words.val.length).erase i)) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
        (hn : 2 ≤ words.val.length) (hk : k.val = (words.val.length : ℤ) - 1), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i : ℕ), i < words.val.length →
              resAt r i =
                (cpLen (selWords words ((Finset.range words.val.length).erase i)) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < len(words) and 0 <= j < len(words), if words[i] = words[j] (equal byte arrays), then r[i] = r[j].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i j : ℕ), i < words.val.length → j < words.val.length →
            wordAt words i = wordAt words j → resAt r i = resAt r j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i j : ℕ), i < words.val.length → j < words.val.length →
              wordAt words i = wordAt words j → resAt r i = resAt r j) := by
    sorry

  /-- Let r1 be the result of the function on input (words, k1) and r2 the result on input (words, k2). Whenever both calls return results, for every i with 0 <= i < len(words), r1[i] >= r2[i].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k1 and k2 are integers with 1 <= k1 <= k2 <= len(words). -/
  theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (k1 k2 : Std.I64)
      (h1 : Pre words k1) (h2 : Pre words k2) (hk : k1.val ≤ k2.val) :
      ∀ r1 r2 : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k1 = ok r1 →
          Aegis.LongestCommonPrefix.longest_common_prefix words k2 = ok r2 →
            ∀ (i : ℕ), i < words.val.length → resAt r2 i ≤ resAt r1 i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k1 k2 : Std.I64)
        (h1 : Pre words k1) (h2 : Pre words k2) (hk : k1.val ≤ k2.val), ∀ r1 r2 : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k1 = ok r1 →
            Aegis.LongestCommonPrefix.longest_common_prefix words k2 = ok r2 →
              ∀ (i : ℕ), i < words.val.length → resAt r2 i ≤ resAt r1 i) := by
    sorry

  /-- Let sigma be a bijection of {0, ..., n-1} and define words_sigma by words_sigma[t] = words[sigma(t)] for 0 <= t < n. Let r = f(words, k) and r_sigma = f(words_sigma, k). Whenever both calls return results, for every i with 0 <= i < n, r_sigma[i] = r[sigma(i)].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with n = len(words) >= 1 and the sum of len(words[j]) over 0 <= j < n at most 10^5; k is an integer with 1 <= k <= n. -/
  theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
      (σ : Equiv.Perm (Fin words.val.length)) (words_σ : Slice (alloc.vec.Vec Std.U8))
      (hσ : words_σ.val =
        (List.finRange words.val.length).map fun t => wordAt words (σ t).val) :
      ∀ r r_σ : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          Aegis.LongestCommonPrefix.longest_common_prefix words_σ k = ok r_σ →
            ∀ (i : ℕ) (hi : i < words.val.length),
              resAt r_σ i = resAt r (σ ⟨i, hi⟩).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
        (σ : Equiv.Perm (Fin words.val.length)) (words_σ : Slice (alloc.vec.Vec Std.U8))
        (hσ : words_σ.val =
          (List.finRange words.val.length).map fun t => wordAt words (σ t).val), ∀ r r_σ : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            Aegis.LongestCommonPrefix.longest_common_prefix words_σ k = ok r_σ →
              ∀ (i : ℕ) (hi : i < words.val.length),
                resAt r_σ i = resAt r (σ ⟨i, hi⟩).val) := by
    sorry

  /-- Whenever both calls f(words, k) and f(words', k) return results r and r', for every i with 0 <= i < n, if the multisets {words[j] : 0 <= j < n and j != i} and {words'[j] : 0 <= j < n and j != i} are equal, then r[i] = r'[i].
    Preconditions: words and words' are slices of nonempty byte strings over lowercase English letters, both of length n >= 1, and the sum of their word lengths is at most 10^5 each; k is an integer with 1 <= k <= n. -/
  theorem spec_11 (words words' : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64)
      (h1 : Pre words k) (h2 : Pre words' k)
      (hn : words'.val.length = words.val.length) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          Aegis.LongestCommonPrefix.longest_common_prefix words' k = ok r' →
            ∀ (i : ℕ) (hi : i < words.val.length) (hi' : i < words'.val.length),
              ((selWords words ((Finset.range words.val.length).erase i) :
                  Multiset (alloc.vec.Vec Std.U8)) =
                (selWords words' ((Finset.range words'.val.length).erase i) :
                  Multiset (alloc.vec.Vec Std.U8))) →
                resAt r i = resAt r' i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64)
        (h1 : Pre words k) (h2 : Pre words' k)
        (hn : words'.val.length = words.val.length), ∀ r r' : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            Aegis.LongestCommonPrefix.longest_common_prefix words' k = ok r' →
              ∀ (i : ℕ) (hi : i < words.val.length) (hi' : i < words'.val.length),
                ((selWords words ((Finset.range words.val.length).erase i) :
                    Multiset (alloc.vec.Vec Std.U8)) =
                  (selWords words' ((Finset.range words'.val.length).erase i) :
                    Multiset (alloc.vec.Vec Std.U8))) →
                  resAt r i = resAt r' i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(words), there exist k distinct indices j_1, ..., j_k with 0 <= j_m < len(words) and j_m != i for all m, such that the common prefix length of {words[j_1], ..., words[j_k]} equals r[i], where the common prefix length of a nonempty set S of strings is the largest L >= 0 such that for every p with 0 <= p < L and every s in S, p < len(s), and for all s, t in S, s[p] = t[p].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words) and len(words) - 1 >= k. -/
  theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
      (hk : k.val ≤ (words.val.length : ℤ) - 1) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i : ℕ), i < words.val.length →
            ∃ I : Finset ℕ,
              I ⊆ Finset.range words.val.length ∧ i ∉ I ∧ I.card = kNat k ∧
                (cpLen (selWords words I) : ℤ) = resAt r i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k)
        (hk : k.val ≤ (words.val.length : ℤ) - 1), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i : ℕ), i < words.val.length →
              ∃ I : Finset ℕ,
                I ⊆ Finset.range words.val.length ∧ i ∉ I ∧ I.card = kNat k ∧
                  (cpLen (selWords words I) : ℤ) = resAt r i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(words) and every subset I of {0, ..., len(words)-1} \ {i} with |I| = k, the common prefix length of {words[j] : j in I} is at most r[i], where the common prefix length of a nonempty set S of strings is the largest L >= 0 such that for every p with 0 <= p < L and every s in S, p < len(s), and for all s, t in S, s[p] = t[p].
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_13 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (i : ℕ), i < words.val.length → ∀ I : Finset ℕ,
            I ⊆ Finset.range words.val.length → i ∉ I → I.card = kNat k →
              (cpLen (selWords words I) : ℤ) ≤ resAt r i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (i : ℕ), i < words.val.length → ∀ I : Finset ℕ,
              I ⊆ Finset.range words.val.length → i ∉ I → I.card = kNat k →
                (cpLen (selWords words I) : ℤ) ≤ resAt r i) := by
    sorry

  /-- Whenever the function returns a result r, if there exist a byte string s and a set J of indices with J subset of {0, ..., len(words)-1}, |J| >= k + 1, and words[j] = s for every j in J, then for every i with 0 <= i < len(words), r[i] >= len(s).
    Preconditions: words is a slice of nonempty byte strings over lowercase English letters with len(words) >= 1 and the sum of len(words[j]) over 0 <= j < len(words) at most 10^5; k is an integer with 1 <= k <= len(words). -/
  theorem spec_14 (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
          ∀ (s : alloc.vec.Vec Std.U8) (J : Finset ℕ),
            J ⊆ Finset.range words.val.length → kNat k + 1 ≤ J.card →
              (∀ j ∈ J, wordAt words j = s) →
                ∀ (i : ℕ), i < words.val.length → (s.val.length : ℤ) ≤ resAt r i := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (k : Std.I64) (hpre : Pre words k), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.LongestCommonPrefix.longest_common_prefix words k = ok r →
            ∀ (s : alloc.vec.Vec Std.U8) (J : Finset ℕ),
              J ⊆ Finset.range words.val.length → kNat k + 1 ≤ J.card →
                (∀ j ∈ J, wordAt words j = s) →
                  ∀ (i : ℕ), i < words.val.length → (s.val.length : ℤ) ≤ resAt r i) := by
    sorry

  end AegisSpec.LongestCommonPrefix
