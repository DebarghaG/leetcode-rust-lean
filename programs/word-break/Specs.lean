import Aegis.WordBreak.Code.Funs

/-!
# Specifications of `Aegis.WordBreak.word_break`

LeetCode problem `word-break`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WordBreak

  def dictWord (wordDict : Slice (alloc.vec.Vec U8)) (i : Nat) : List U8 :=
    match wordDict.val[i]? with
    | some w => w.val
    | none => []

  def AllLower (l : List U8) : Prop :=
    ∀ b ∈ l, 97 ≤ b.val ∧ b.val ≤ 122

  def StringConstraints (s : Slice U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 300 ∧ AllLower s.val

  def DictConstraints (wordDict : Slice (alloc.vec.Vec U8)) : Prop :=
    1 ≤ wordDict.val.length ∧ wordDict.val.length ≤ 1000 ∧
    (∀ i, i < wordDict.val.length →
      1 ≤ (dictWord wordDict i).length ∧ (dictWord wordDict i).length ≤ 20 ∧
      AllLower (dictWord wordDict i)) ∧
    (∀ i j, i < wordDict.val.length → j < wordDict.val.length → i ≠ j →
      dictWord wordDict i ≠ dictWord wordDict j)

  def Constraints (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8)) : Prop :=
    StringConstraints s ∧ DictConstraints wordDict

  def Segments (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (idx : List Nat) : Prop :=
    idx ≠ [] ∧ (∀ i ∈ idx, i < wordDict.val.length) ∧
      (idx.map (dictWord wordDict)).flatten = s.val

  def IsPrefix (w : List U8) (s : Slice U8) : Prop :=
    w.length ≤ s.val.length ∧ ∀ t, t < w.length → w[t]? = s.val[t]?

  def IsSuffix (w : List U8) (s : Slice U8) : Prop :=
    w.length ≤ s.val.length ∧
      ∀ t, t < w.length → w[t]? = s.val[s.val.length - w.length + t]?

  def dropSlice (s : Slice U8) (n : Nat) : Slice U8 :=
    ⟨(s.val.drop n).length, Aeneas.Data.ListN.ListN.fromList (s.val.drop n), by
      have h1 : (s.val.drop n).length = s.val.length - n := List.length_drop
      have h2 : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
      have h3 : s.leng ≤ Usize.max := s.bound
      omega⟩

  def IsPermutation (wordDict wordDict' : Slice (alloc.vec.Vec U8)) : Prop :=
    wordDict.val.length = wordDict'.val.length ∧
      ∃ f : Fin wordDict.val.length → Fin wordDict'.val.length,
        Function.Bijective f ∧
          ∀ i : Fin wordDict.val.length,
            dictWord wordDict (i : Nat) = dictWord wordDict' (f i : Nat)

  def OccursIn (wordDict : Slice (alloc.vec.Vec U8)) (w : List U8) : Prop :=
    ∃ i, i < wordDict.val.length ∧ dictWord wordDict i = w

  /-- Whenever word_break(s, wordDict) returns Ok r, r = true if and only if there exist an integer k >= 1 and indices i_1, ..., i_k with 0 <= i_j < len(wordDict) such that s is the concatenation of the byte arrays wordDict[i_1], ..., wordDict[i_k] (indices may be repeated). Equivalently, there exist cut positions 0 = p_0 < p_1 < ... < p_k = len(s) such that for every j in [1,k], the block of bytes s[p_{j-1}], ..., s[p_j - 1] equals wordDict[i_j] for some i_j in [0,len(wordDict)).
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_1 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      ∀ r : Bool, Aegis.WordBreak.word_break s wordDict = ok r →
        (r = true ↔ ∃ idx : List Nat, Segments s wordDict idx) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), ∀ r : Bool, Aegis.WordBreak.word_break s wordDict = ok r →
          (r = true ↔ ∃ idx : List Nat, Segments s wordDict idx)) := by
    sorry

  /-- For every input satisfying the preconditions, word_break(s, wordDict) returns Ok r for some Bool r; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_2 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      ∃ r : Bool, Aegis.WordBreak.word_break s wordDict = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), ∃ r : Bool, Aegis.WordBreak.word_break s wordDict = ok r) := by
    sorry

  /-- Whenever word_break(s, wordDict) returns Ok true, there exist an integer k with 1 <= k <= len(s), indices i_1, ..., i_k with 0 <= i_j < len(wordDict), and cut positions 0 = p_0 < p_1 < ... < p_k = len(s) such that for every j in [1,k], len(wordDict[i_j]) = p_j - p_{j-1} and for every t with 0 <= t < p_j - p_{j-1}, wordDict[i_j][t] = s[p_{j-1} + t].
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_3 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      Aegis.WordBreak.word_break s wordDict = ok true →
        ∃ (k : Nat) (idx : Fin k → Nat) (p : Fin (k + 1) → Nat),
          1 ≤ k ∧ k ≤ s.val.length ∧
          p ⟨0, Nat.succ_pos k⟩ = 0 ∧
          p ⟨k, Nat.lt_succ_self k⟩ = s.val.length ∧
          (∀ j : Fin k, p j.castSucc < p j.succ) ∧
          (∀ j : Fin k,
            idx j < wordDict.val.length ∧
            (dictWord wordDict (idx j)).length = p j.succ - p j.castSucc ∧
            (∀ t : Nat, t < p j.succ - p j.castSucc →
              (dictWord wordDict (idx j))[t]? = s.val[p j.castSucc + t]?)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), Aegis.WordBreak.word_break s wordDict = ok true →
          ∃ (k : Nat) (idx : Fin k → Nat) (p : Fin (k + 1) → Nat),
            1 ≤ k ∧ k ≤ s.val.length ∧
            p ⟨0, Nat.succ_pos k⟩ = 0 ∧
            p ⟨k, Nat.lt_succ_self k⟩ = s.val.length ∧
            (∀ j : Fin k, p j.castSucc < p j.succ) ∧
            (∀ j : Fin k,
              idx j < wordDict.val.length ∧
              (dictWord wordDict (idx j)).length = p j.succ - p j.castSucc ∧
              (∀ t : Nat, t < p j.succ - p j.castSucc →
                (dictWord wordDict (idx j))[t]? = s.val[p j.castSucc + t]?))) := by
    sorry

  /-- Whenever word_break(s, wordDict) returns Ok true, for every position t with 0 <= t < len(s) there exist an index i with 0 <= i < len(wordDict) and a position u with 0 <= u < len(wordDict[i]) such that wordDict[i][u] = s[t].
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_4 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      Aegis.WordBreak.word_break s wordDict = ok true →
        ∀ t : Nat, t < s.val.length →
          ∃ i u : Nat, i < wordDict.val.length ∧
            u < (dictWord wordDict i).length ∧
            (dictWord wordDict i)[u]? = s.val[t]? := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), Aegis.WordBreak.word_break s wordDict = ok true →
          ∀ t : Nat, t < s.val.length →
            ∃ i u : Nat, i < wordDict.val.length ∧
              u < (dictWord wordDict i).length ∧
              (dictWord wordDict i)[u]? = s.val[t]?) := by
    sorry

  /-- Whenever word_break(s, wordDict) returns Ok r and word_break(s, wordDict') returns Ok r', we have r = r'.
    Preconditions: The input (s, wordDict) satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. Let wordDict' be any slice of Vec U8 satisfying the same dictionary constraints and suppose wordDict' is a permutation of wordDict: len(wordDict') = len(wordDict) and there is a bijection f from {0,...,len(wordDict)-1} to {0,...,len(wordDict')-1} such that wordDict[i] = wordDict'[f(i)] for every i. -/
  theorem spec_5 (s : Slice U8) (wordDict wordDict' : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) (hd' : DictConstraints wordDict')
      (hperm : IsPermutation wordDict wordDict') :
      ∀ r r' : Bool,
        Aegis.WordBreak.word_break s wordDict = ok r →
        Aegis.WordBreak.word_break s wordDict' = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (wordDict wordDict' : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict) (hd' : DictConstraints wordDict')
        (hperm : IsPermutation wordDict wordDict'), ∀ r r' : Bool,
          Aegis.WordBreak.word_break s wordDict = ok r →
          Aegis.WordBreak.word_break s wordDict' = ok r' → r = r') := by
    sorry

  /-- Whenever word_break(s, wordDict) returns Ok true, there exist an integer k >= 1 and indices i_1, ..., i_k with 0 <= i_j < len(wordDict) such that len(s) = len(wordDict[i_1]) + ... + len(wordDict[i_k]).
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_6 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      Aegis.WordBreak.word_break s wordDict = ok true →
        ∃ (k : Nat) (idx : Fin k → Nat),
          1 ≤ k ∧ (∀ j : Fin k, idx j < wordDict.val.length) ∧
          s.val.length = ∑ j : Fin k, (dictWord wordDict (idx j)).length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), Aegis.WordBreak.word_break s wordDict = ok true →
          ∃ (k : Nat) (idx : Fin k → Nat),
            1 ≤ k ∧ (∀ j : Fin k, idx j < wordDict.val.length) ∧
            s.val.length = ∑ j : Fin k, (dictWord wordDict (idx j)).length) := by
    sorry

  /-- Whenever word_break(s, wordDict) returns Ok true, there exists an index i with 0 <= i < len(wordDict) such that wordDict[i] is a suffix of s, meaning len(wordDict[i]) <= len(s) and for every t with 0 <= t < len(wordDict[i]), wordDict[i][t] = s[len(s) - len(wordDict[i]) + t].
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_7 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      Aegis.WordBreak.word_break s wordDict = ok true →
        ∃ i : Nat, i < wordDict.val.length ∧ IsSuffix (dictWord wordDict i) s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), Aegis.WordBreak.word_break s wordDict = ok true →
          ∃ i : Nat, i < wordDict.val.length ∧ IsSuffix (dictWord wordDict i) s) := by
    sorry

  /-- For every input satisfying the preconditions, word_break(s, wordDict) returns Ok true if and only if there exists an index i with 0 <= i < len(wordDict) such that wordDict[i] is a prefix of s (i.e., len(wordDict[i]) <= len(s) and for every t with 0 <= t < len(wordDict[i]), wordDict[i][t] = s[t]) and either len(wordDict[i]) = len(s) or (len(wordDict[i]) < len(s) and word_break(s[len(wordDict[i])..], wordDict) returns Ok true).
    Preconditions: The input satisfies the problem constraints: 1 <= len(s) <= 300; 1 <= len(wordDict) <= 1000; every wordDict[i] has length between 1 and 20 and consists only of lowercase ASCII bytes 'a'..'z'; s consists only of lowercase ASCII bytes 'a'..'z'; and all words wordDict[0], ..., wordDict[len(wordDict)-1] are pairwise distinct. -/
  theorem spec_8 (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
      (h : Constraints s wordDict) :
      (Aegis.WordBreak.word_break s wordDict = ok true) ↔
        ∃ i : Nat, i < wordDict.val.length ∧ IsPrefix (dictWord wordDict i) s ∧
          ((dictWord wordDict i).length = s.val.length ∨
            ((dictWord wordDict i).length < s.val.length ∧
             Aegis.WordBreak.word_break
               (dropSlice s (dictWord wordDict i).length) wordDict = ok true)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (wordDict : Slice (alloc.vec.Vec U8))
        (h : Constraints s wordDict), (Aegis.WordBreak.word_break s wordDict = ok true) ↔
          ∃ i : Nat, i < wordDict.val.length ∧ IsPrefix (dictWord wordDict i) s ∧
            ((dictWord wordDict i).length = s.val.length ∨
              ((dictWord wordDict i).length < s.val.length ∧
               Aegis.WordBreak.word_break
                 (dropSlice s (dictWord wordDict i).length) wordDict = ok true))) := by
    sorry

  end AegisSpec.WordBreak
