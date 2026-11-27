import Aegis.BagOfTokensScore.Code.Funs

/-!
# Specifications of `Aegis.BagOfTokensScore.bag_of_tokens_score`

LeetCode problem `bag-of-tokens`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BagOfTokensScore

  inductive MoveDir where

    | faceUp

    | faceDown
    deriving DecidableEq, Repr

  abbrev Move : Type := Nat × MoveDir

  abbrev PlaySeq : Type := List Move

  def valAt (l : List ℤ) (i : Nat) : ℤ := (l[i]?).getD 0

  def tokenVals (tokens : Slice I64) : List ℤ := tokens.val.map (fun x => x.val)

  def tokAt (l : List I64) (i : Nat) : ℤ := valAt (l.map (fun x => x.val)) i

  def runFrom (tokens : List ℤ) (p s : ℤ) : PlaySeq → ℤ × ℤ
    | [] => (p, s)
    | (i, d) :: rest =>
        match d with
        | MoveDir.faceUp => runFrom tokens (p - valAt tokens i) (s + 1) rest
        | MoveDir.faceDown => runFrom tokens (p + valAt tokens i) (s - 1) rest

  def ValidFrom (tokens : List ℤ) (p s : ℤ) (used : List Nat) : PlaySeq → Prop
    | [] => True
    | (i, d) :: rest =>
        i < tokens.length ∧ i ∉ used ∧
          (match d with
           | MoveDir.faceUp =>
               valAt tokens i ≤ p ∧
                 ValidFrom tokens (p - valAt tokens i) (s + 1) (i :: used) rest
           | MoveDir.faceDown =>
               1 ≤ s ∧ ValidFrom tokens (p + valAt tokens i) (s - 1) (i :: used) rest)

  def ValidPlay (tokens : List ℤ) (power : ℤ) (moves : PlaySeq) : Prop :=
    ValidFrom tokens power 0 [] moves

  def finalScore (tokens : List ℤ) (power : ℤ) (moves : PlaySeq) : ℤ :=
    (runFrom tokens power 0 moves).2

  def Achieved (tokens : List ℤ) (power : ℤ) (s : ℤ) : Prop :=
    ∃ moves : PlaySeq, ValidPlay tokens power moves ∧ finalScore tokens power moves = s

  def IsMaxScore (tokens : List ℤ) (power : ℤ) (m : ℤ) : Prop :=
    Achieved tokens power m ∧ ∀ s : ℤ, Achieved tokens power s → s ≤ m

  noncomputable def M (tokens : List ℤ) (power : ℤ) : ℤ :=
    by
      classical
      exact if h : ∃ m : ℤ, IsMaxScore tokens power m then h.choose else 0

  def EndsFaceUp (moves : PlaySeq) : Prop :=
    ∃ (init : PlaySeq) (i : Nat), moves = init ++ [(i, MoveDir.faceUp)]

  def zeroCount (l : List I64) : Nat := (l.filter (fun x => x.val = 0)).length

  def dropZeros (tokens : Slice I64) : List ℤ :=
    (tokens.val.filter (fun x => x.val ≠ 0)).map (fun x => x.val)

  /-- The function returns a result r and r equals M(tokens, power), where M(tokens, power) is the maximum final score over all valid play sequences defined as follows. A play sequence is a finite sequence of moves, each move selecting a not-yet-selected index i and a direction. Initially power_0 = power and score_0 = 0. A face-up move on i requires current power >= tokens[i] and changes the state to (power - tokens[i], score + 1). A face-down move on i requires current score >= 1 and changes the state to (power + tokens[i], score - 1). A token index may be selected at most once. The empty sequence is allowed. The final score is the score after the last move. M is the maximum of these final scores over all valid play sequences.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_1 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∃ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧
          r.val = M (tokenVals tokens) power.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∃ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧
            r.val = M (tokenVals tokens) power.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, overflow, or access an out-of-bounds index).
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_2 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∃ r : I64, Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∃ r : I64, Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(tokens).
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_3 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∀ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
          0 ≤ r.val ∧ r.val ≤ ((Slice.len tokens).val : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∀ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
            0 ≤ r.val ∧ r.val ≤ ((Slice.len tokens).val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a valid play sequence under the rules defined in spec_1 whose final score is exactly r.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_4 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∀ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
          ∃ moves : PlaySeq,
            ValidPlay (tokenVals tokens) power.val moves ∧
              finalScore (tokenVals tokens) power.val moves = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∀ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
            ∃ moves : PlaySeq,
              ValidPlay (tokenVals tokens) power.val moves ∧
                finalScore (tokenVals tokens) power.val moves = r.val) := by
    sorry

  /-- Whenever the function returns a result r, every valid play sequence under the rules defined in spec_1 has final score at most r.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_5 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∀ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
          ∀ moves : PlaySeq,
            ValidPlay (tokenVals tokens) power.val moves →
              finalScore (tokenVals tokens) power.val moves ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∀ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
            ∀ moves : PlaySeq,
              ValidPlay (tokenVals tokens) power.val moves →
                finalScore (tokenVals tokens) power.val moves ≤ r.val) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; 0 <= power < 10000; len(tokens) > 0; and for every i with 0 <= i < len(tokens), tokens[i] > power. -/
  theorem spec_6 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000)
      (hne : 0 < (Slice.len tokens).val)
      (hall : ∀ i : Nat, i < (Slice.len tokens).val → power.val < tokAt tokens.val i) :
      ∃ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000)
        (hne : 0 < (Slice.len tokens).val)
        (hall : ∀ i : Nat, i < (Slice.len tokens).val → power.val < tokAt tokens.val i), ∃ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns r with r >= 1.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; 0 <= power < 10000; and there exists i with 0 <= i < len(tokens) and tokens[i] <= power. -/
  theorem spec_7 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000)
      (hex : ∃ i : Nat, i < (Slice.len tokens).val ∧ tokAt tokens.val i ≤ power.val) :
      ∃ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000)
        (hex : ∃ i : Nat, i < (Slice.len tokens).val ∧ tokAt tokens.val i ≤ power.val), ∃ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- Let S = sum_{i=0}^{len(tokens)-1} tokens[i]. The function returns r = len(tokens) if and only if S <= power.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_8 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∃ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧
          (r.val = ((Slice.len tokens).val : ℤ) ↔
            (tokenVals tokens).sum ≤ power.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∃ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧
            (r.val = ((Slice.len tokens).val : ℤ) ↔
              (tokenVals tokens).sum ≤ power.val)) := by
    sorry

  /-- If r1 is the result returned for (tokens1, power) and r2 is the result returned for (tokens2, power), then r1 = r2.
    Preconditions: tokens1 and tokens2 are slices satisfying 0 <= len(tokens1) = len(tokens2) <= 1000 and, for every i, 0 <= tokens1[i] < 10000 and 0 <= tokens2[i] < 10000; 0 <= power < 10000; and tokens2 is a permutation of tokens1, meaning there exists a permutation pi of {0,...,len(tokens1)-1} such that tokens2[i] = tokens1[pi(i)] for every i. -/
  theorem spec_9 (tokens1 tokens2 : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens1).val ∧ (Slice.len tokens1).val ≤ 1000)
      (hlen_eq : (Slice.len tokens1).val = (Slice.len tokens2).val)
      (htok1 : ∀ i : Nat, i < (Slice.len tokens1).val →
        0 ≤ tokAt tokens1.val i ∧ tokAt tokens1.val i < 10000)
      (htok2 : ∀ i : Nat, i < (Slice.len tokens2).val →
        0 ≤ tokAt tokens2.val i ∧ tokAt tokens2.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000)
      (hperm : ∃ pi : Equiv.Perm (Fin tokens1.val.length),
        ∀ i : Fin tokens2.val.length,
          tokens2.val.get i = tokens1.val.get (pi (Fin.cast hlen_eq.symm i))) :
      ∀ r1 r2 : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens1 power = ok r1 →
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens2 power = ok r2 →
            r1.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tokens1 tokens2 : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens1).val ∧ (Slice.len tokens1).val ≤ 1000)
        (hlen_eq : (Slice.len tokens1).val = (Slice.len tokens2).val)
        (htok1 : ∀ i : Nat, i < (Slice.len tokens1).val →
          0 ≤ tokAt tokens1.val i ∧ tokAt tokens1.val i < 10000)
        (htok2 : ∀ i : Nat, i < (Slice.len tokens2).val →
          0 ≤ tokAt tokens2.val i ∧ tokAt tokens2.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000)
        (hperm : ∃ pi : Equiv.Perm (Fin tokens1.val.length),
          ∀ i : Fin tokens2.val.length,
            tokens2.val.get i = tokens1.val.get (pi (Fin.cast hlen_eq.symm i))), ∀ r1 r2 : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens1 power = ok r1 →
            Aegis.BagOfTokensScore.bag_of_tokens_score tokens2 power = ok r2 →
              r1.val = r2.val) := by
    sorry

  /-- If r1 is the result returned for (tokens, p1) and r2 is the result returned for (tokens, p2), then r1 <= r2.
    Preconditions: tokens satisfies 0 <= len(tokens) <= 1000 and, for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= p1 <= p2 < 10000. -/
  theorem spec_10 (tokens : Slice I64) (p1 p2 : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ p1.val ∧ p1.val ≤ p2.val ∧ p2.val < 10000) :
      ∀ r1 r2 : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens p1 = ok r1 →
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens p2 = ok r2 →
            r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tokens : Slice I64) (p1 p2 : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ p1.val ∧ p1.val ≤ p2.val ∧ p2.val < 10000), ∀ r1 r2 : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens p1 = ok r1 →
            Aegis.BagOfTokensScore.bag_of_tokens_score tokens p2 = ok r2 →
              r1.val ≤ r2.val) := by
    sorry

  /-- Let z be the number of indices i with 0 <= i < len(tokens) and tokens[i] = 0, and let tokens' be the slice obtained by deleting all entries equal to 0 from tokens. If r is the result returned for (tokens, power), then r >= z + M(tokens', power), where M is the maximum final score over all valid play sequences under the rules defined in spec_1.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_11 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∃ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧
          (zeroCount tokens.val : ℤ) + M (dropZeros tokens) power.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∃ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r ∧
            (zeroCount tokens.val : ℤ) + M (dropZeros tokens) power.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists a valid play sequence under the rules defined in spec_1 with final score r whose last move is a face-up move.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_12 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∀ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r → 0 < r.val →
          ∃ moves : PlaySeq,
            ValidPlay (tokenVals tokens) power.val moves ∧
              finalScore (tokenVals tokens) power.val moves = r.val ∧ EndsFaceUp moves := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∀ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r → 0 < r.val →
            ∃ moves : PlaySeq,
              ValidPlay (tokenVals tokens) power.val moves ∧
                finalScore (tokenVals tokens) power.val moves = r.val ∧ EndsFaceUp moves) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k <= r there exists a finite valid play sequence under the rules defined in spec_1 whose final score is exactly k.
    Preconditions: 0 <= len(tokens) <= 1000; for every i with 0 <= i < len(tokens), 0 <= tokens[i] < 10000; and 0 <= power < 10000. -/
  theorem spec_13 (tokens : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
      (htok : ∀ i : Nat, i < (Slice.len tokens).val →
        0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000) :
      ∀ r : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
          ∀ k : ℤ, 0 ≤ k → k ≤ r.val →
            ∃ moves : PlaySeq,
              ValidPlay (tokenVals tokens) power.val moves ∧
                finalScore (tokenVals tokens) power.val moves = k := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (tokens : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens).val ∧ (Slice.len tokens).val ≤ 1000)
        (htok : ∀ i : Nat, i < (Slice.len tokens).val →
          0 ≤ tokAt tokens.val i ∧ tokAt tokens.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000), ∀ r : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens power = ok r →
            ∀ k : ℤ, 0 ≤ k → k ≤ r.val →
              ∃ moves : PlaySeq,
                ValidPlay (tokenVals tokens) power.val moves ∧
                  finalScore (tokenVals tokens) power.val moves = k) := by
    sorry

  /-- If r1 is the result returned for (tokens1, power) and r2 is the result returned for (tokens2, power), then r1 <= r2.
    Preconditions: tokens1 and tokens2 are slices satisfying 0 <= len(tokens1) <= 1000, len(tokens2) = len(tokens1) + 1, all token values lie in [0,10000), and 0 <= power < 10000; tokens2 is obtained from tokens1 by inserting one additional token value v with 0 <= v < 10000. -/
  theorem spec_14 (tokens1 tokens2 : Slice I64) (power : I64)
      (hlen : 0 ≤ (Slice.len tokens1).val ∧ (Slice.len tokens1).val ≤ 1000)
      (hlen2 : (Slice.len tokens2).val = (Slice.len tokens1).val + 1)
      (htok1 : ∀ i : Nat, i < (Slice.len tokens1).val →
        0 ≤ tokAt tokens1.val i ∧ tokAt tokens1.val i < 10000)
      (htok2 : ∀ i : Nat, i < (Slice.len tokens2).val →
        0 ≤ tokAt tokens2.val i ∧ tokAt tokens2.val i < 10000)
      (hpow : 0 ≤ power.val ∧ power.val < 10000)
      (hins : ∃ (i : Nat) (v : I64),
        0 ≤ v.val ∧ v.val < 10000 ∧ i ≤ tokens1.val.length ∧
          tokens2.val = tokens1.val.take i ++ [v] ++ tokens1.val.drop i) :
      ∀ r1 r2 : I64,
        Aegis.BagOfTokensScore.bag_of_tokens_score tokens1 power = ok r1 →
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens2 power = ok r2 →
            r1.val ≤ r2.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (tokens1 tokens2 : Slice I64) (power : I64)
        (hlen : 0 ≤ (Slice.len tokens1).val ∧ (Slice.len tokens1).val ≤ 1000)
        (hlen2 : (Slice.len tokens2).val = (Slice.len tokens1).val + 1)
        (htok1 : ∀ i : Nat, i < (Slice.len tokens1).val →
          0 ≤ tokAt tokens1.val i ∧ tokAt tokens1.val i < 10000)
        (htok2 : ∀ i : Nat, i < (Slice.len tokens2).val →
          0 ≤ tokAt tokens2.val i ∧ tokAt tokens2.val i < 10000)
        (hpow : 0 ≤ power.val ∧ power.val < 10000)
        (hins : ∃ (i : Nat) (v : I64),
          0 ≤ v.val ∧ v.val < 10000 ∧ i ≤ tokens1.val.length ∧
            tokens2.val = tokens1.val.take i ++ [v] ++ tokens1.val.drop i), ∀ r1 r2 : I64,
          Aegis.BagOfTokensScore.bag_of_tokens_score tokens1 power = ok r1 →
            Aegis.BagOfTokensScore.bag_of_tokens_score tokens2 power = ok r2 →
              r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.BagOfTokensScore
