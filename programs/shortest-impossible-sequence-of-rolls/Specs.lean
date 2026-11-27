import Aegis.ShortestSequence.Code.Funs

/-!
# Specifications of `Aegis.ShortestSequence.shortest_sequence`

LeetCode problem `shortest-impossible-sequence-of-rolls`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ShortestSequence

  def OccursIn (v : ℤ) (l : List Std.I64) : Prop := ∃ x ∈ l, x.val = v

  def ValuesIn (k : ℤ) (s : List Std.I64) : Prop := ∀ v ∈ s, 1 ≤ v.val ∧ v.val ≤ k

  def IsSubsequence (s rolls : List Std.I64) : Prop := List.Sublist s rolls

  def MissingSeq (k : ℤ) (rolls : List Std.I64) (L : ℕ) : Prop :=
    ∃ s : List Std.I64, s.length = L ∧ ValuesIn k s ∧ ¬ IsSubsequence s rolls

  def UniversalLen (k : ℤ) (rolls : List Std.I64) (L : ℕ) : Prop :=
    ∀ s : List Std.I64, s.length = L → ValuesIn k s → IsSubsequence s rolls

  def occurrences (l : List Std.I64) (v : ℤ) : ℕ := (l.filter (fun x => x.val = v)).length

  def CoversAll (k : ℤ) (s : List Std.I64) : Prop := ∀ v : ℤ, 1 ≤ v → v ≤ k → OccursIn v s

  def subarray (l : List Std.I64) (a b : ℕ) : List Std.I64 := (l.drop a).take (b + 1 - a)

  def intervalDisjoint (p q : ℕ × ℕ) : Prop := p.2 < q.1 ∨ q.2 < p.1

  def BlocksCovering (k : ℤ) (rolls : List Std.I64) (n : ℕ) : Prop :=
    ∃ bs : List (ℕ × ℕ),
      bs.length = n ∧
        (∀ p ∈ bs, p.1 ≤ p.2 ∧ p.2 < rolls.length) ∧
        bs.Pairwise intervalDisjoint ∧
        (∀ p ∈ bs, CoversAll k (subarray rolls p.1 p.2))

  /-- The function returns a result r and r is the least positive integer L for which there exists a finite sequence s of length L such that every s[j] is in {1,...,k} and s is not a subsequence of rolls. A sequence s is a subsequence of rolls exactly when there are indices 0 <= i_0 < i_1 < ... < i_{len(s)-1} < len(rolls) with rolls[i_j] = s[j] for all j; the empty sequence is a subsequence of every rolls. Equivalently: r >= 1; there exists a length-r sequence over {1,...,k} that is not a subsequence of rolls; and for every integer L with 1 <= L < r, every length-L sequence over {1,...,k} is a subsequence of rolls.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_1 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          1 ≤ r.val ∧
          MissingSeq k.val rolls.val r.val.toNat ∧
          (∀ L : ℕ, 1 ≤ L → L < r.val.toNat → UniversalLen k.val rolls.val L) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            1 ≤ r.val ∧
            MissingSeq k.val rolls.val r.val.toNat ∧
            (∀ L : ℕ, 1 ≤ L → L < r.val.toNat → UniversalLen k.val rolls.val L)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_2 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64, Aegis.ShortestSequence.shortest_sequence rolls k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64, Aegis.ShortestSequence.shortest_sequence rolls k = ok r) := by
    sorry

  /-- The function returns a result r with 1 <= r <= len(rolls) + 1.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_3 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (rolls.val.length : ℤ) + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            1 ≤ r.val ∧ r.val ≤ (rolls.val.length : ℤ) + 1) := by
    sorry

  /-- The function returns a result r with r <= (integer floor of len(rolls) divided by k) + 1.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_4 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          r.val ≤ ((rolls.val.length / k.val.toNat : ℕ) : ℤ) + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            r.val ≤ ((rolls.val.length / k.val.toNat : ℕ) : ℤ) + 1) := by
    sorry

  /-- The function returns a result r. Then r = 1 if and only if there exists an integer v with 1 <= v <= k such that v does not occur in rolls (that is, rolls[i] != v for every i with 0 <= i < len(rolls)).
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_5 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          (r.val = 1 ↔ ∃ v : ℤ, 1 ≤ v ∧ v ≤ k.val ∧ ¬ OccursIn v rolls.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            (r.val = 1 ↔ ∃ v : ℤ, 1 ≤ v ∧ v ≤ k.val ∧ ¬ OccursIn v rolls.val)) := by
    sorry

  /-- The function returns a result r and r = len(rolls) + 1.
    Preconditions: len(rolls) >= 1; k = 1; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k (so rolls[i] = 1). -/
  theorem spec_6 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk : k.val = 1) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          r.val = (rolls.val.length : ℤ) + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk : k.val = 1) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            r.val = (rolls.val.length : ℤ) + 1) := by
    sorry

  /-- The function returns a result r and there exists a sequence s of length r such that every s[j] is in {1,...,k} and s is not a subsequence of rolls.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_7 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          MissingSeq k.val rolls.val r.val.toNat := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            MissingSeq k.val rolls.val r.val.toNat) := by
    sorry

  /-- The function returns a result r and, for every integer L with 1 <= L < r, every sequence s of length L such that every s[j] is in {1,...,k} is a subsequence of rolls.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_8 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          ∀ L : ℕ, 1 ≤ L → L < r.val.toNat → UniversalLen k.val rolls.val L := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            ∀ L : ℕ, 1 ≤ L → L < r.val.toNat → UniversalLen k.val rolls.val L) := by
    sorry

  /-- The function returns a result r. Let M be the maximum number of pairwise disjoint nonempty contiguous subarrays of rolls such that each chosen subarray contains every value in {1,...,k} at least once. Then r = M + 1. A contiguous subarray is given by indices a,b with 0 <= a <= b < len(rolls); two chosen subarrays are disjoint when no index belongs to both.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_9 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          ∃ M : ℕ,
            IsGreatest {n : ℕ | BlocksCovering k.val rolls.val n} M ∧ r.val = (M : ℤ) + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            ∃ M : ℕ,
              IsGreatest {n : ℕ | BlocksCovering k.val rolls.val n} M ∧ r.val = (M : ℤ) + 1) := by
    sorry

  /-- Under these preconditions, the function returns a result r for (rolls,k) and a result r' for (rolls',k), and r' >= r.
    Preconditions: For (rolls,k): len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; and 1 <= rolls[i] <= k for all i. Let extra be any finite list of integers such that every extra[j] is in {1,...,k} and len(rolls)+len(extra) <= 100000; set rolls' = rolls followed by extra. Then (rolls',k) also satisfies the constraints with len(rolls') >= 1. -/
  theorem spec_10 (rolls : Slice Std.I64) (k : Std.I64) (extra : List Std.I64)
      (rolls' : Slice Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
      (hextra : ValuesIn k.val extra)
      (htotal : rolls.val.length + extra.length ≤ 100000)
      (hrolls' : rolls'.val = rolls.val ++ extra) :
      ∃ r r' : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          Aegis.ShortestSequence.shortest_sequence rolls' k = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64) (extra : List Std.I64)
        (rolls' : Slice Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
        (hextra : ValuesIn k.val extra)
        (htotal : rolls.val.length + extra.length ≤ 100000)
        (hrolls' : rolls'.val = rolls.val ++ extra), ∃ r r' : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            Aegis.ShortestSequence.shortest_sequence rolls' k = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  /-- Under these preconditions, the function returns a result r for (rolls,k) and a result r' for (rolls',k), and r' <= r.
    Preconditions: For (rolls,k): len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; and 1 <= rolls[i] <= k for all i. Let rolls' be any nonempty list obtained by deleting zero or more entries from rolls while preserving order, so len(rolls') >= 1 and 1 <= rolls'[i] <= k for all i. -/
  theorem spec_11 (rolls : Slice Std.I64) (k : Std.I64) (rolls' : Slice Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
      (hlen1' : 1 ≤ rolls'.val.length)
      (hsub : IsSubsequence rolls'.val rolls.val) :
      ∃ r r' : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          Aegis.ShortestSequence.shortest_sequence rolls' k = ok r' ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64) (rolls' : Slice Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
        (hlen1' : 1 ≤ rolls'.val.length)
        (hsub : IsSubsequence rolls'.val rolls.val), ∃ r r' : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            Aegis.ShortestSequence.shortest_sequence rolls' k = ok r' ∧ r'.val ≤ r.val) := by
    sorry

  /-- Under these preconditions, the function returns a result r1 for (rolls,k1) and a result r2 for (rolls,k2), and r2 <= r1.
    Preconditions: Let k1 and k2 be integers with 1 <= k1 <= k2 <= 100000. Let rolls be a nonempty list with len(rolls) <= 100000 and 1 <= rolls[i] <= k1 for every i. Then (rolls,k1) and (rolls,k2) both satisfy the input constraints. -/
  theorem spec_12 (rolls : Slice Std.I64) (k1 k2 : Std.I64)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
      (hlen1 : 1 ≤ rolls.val.length) (hlen2 : rolls.val.length ≤ 100000)
      (hvals : ValuesIn k1.val rolls.val) :
      ∃ r1 r2 : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k1 = ok r1 ∧
          Aegis.ShortestSequence.shortest_sequence rolls k2 = ok r2 ∧ r2.val ≤ r1.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k1 k2 : Std.I64)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 100000)
        (hlen1 : 1 ≤ rolls.val.length) (hlen2 : rolls.val.length ≤ 100000)
        (hvals : ValuesIn k1.val rolls.val), ∃ r1 r2 : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k1 = ok r1 ∧
            Aegis.ShortestSequence.shortest_sequence rolls k2 = ok r2 ∧ r2.val ≤ r1.val) := by
    sorry

  /-- Under these preconditions, the function returns a result r for (rolls,k) and a result r_rev for (rolls_rev,k), and r_rev = r.
    Preconditions: For (rolls,k): len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; and 1 <= rolls[i] <= k for all i. Let rolls_rev be the list of the same length with rolls_rev[i] = rolls[len(rolls)-1-i] for 0 <= i < len(rolls). -/
  theorem spec_13 (rolls : Slice Std.I64) (k : Std.I64) (rolls_rev : Slice Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
      (hrev : rolls_rev.val = rolls.val.reverse) :
      ∃ r r_rev : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          Aegis.ShortestSequence.shortest_sequence rolls_rev k = ok r_rev ∧
            r_rev.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64) (rolls_rev : Slice Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
        (hrev : rolls_rev.val = rolls.val.reverse), ∃ r r_rev : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            Aegis.ShortestSequence.shortest_sequence rolls_rev k = ok r_rev ∧
              r_rev.val = r.val) := by
    sorry

  /-- Under these preconditions, the function returns a result r for (rolls,k) and a result r_pi for (rolls_pi,k), and r_pi = r.
    Preconditions: For (rolls,k): len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; and 1 <= rolls[i] <= k for all i. Let pi be any bijection from {1,...,k} to itself, and let rolls_pi be defined by rolls_pi[i] = pi(rolls[i]) for every 0 <= i < len(rolls). -/
  theorem spec_14 (rolls : Slice Std.I64) (k : Std.I64) (pi : Std.I64 → Std.I64)
      (rolls_pi : Slice Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
      (hpi_maps : ∀ v : Std.I64, 1 ≤ v.val → v.val ≤ k.val →
        1 ≤ (pi v).val ∧ (pi v).val ≤ k.val)
      (hpi_inj : ∀ v w : Std.I64, 1 ≤ v.val → v.val ≤ k.val → 1 ≤ w.val → w.val ≤ k.val →
        pi v = pi w → v = w)
      (hpi : rolls_pi.val = rolls.val.map pi) :
      ∃ r r_pi : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          Aegis.ShortestSequence.shortest_sequence rolls_pi k = ok r_pi ∧
            r_pi.val = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64) (pi : Std.I64 → Std.I64)
        (rolls_pi : Slice Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val)
        (hpi_maps : ∀ v : Std.I64, 1 ≤ v.val → v.val ≤ k.val →
          1 ≤ (pi v).val ∧ (pi v).val ≤ k.val)
        (hpi_inj : ∀ v w : Std.I64, 1 ≤ v.val → v.val ≤ k.val → 1 ≤ w.val → w.val ≤ k.val →
          pi v = pi w → v = w)
        (hpi : rolls_pi.val = rolls.val.map pi), ∃ r r_pi : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            Aegis.ShortestSequence.shortest_sequence rolls_pi k = ok r_pi ∧
              r_pi.val = r.val) := by
    sorry

  /-- The function returns a result r and, for every v with 1 <= v <= k, the number of indices i with 0 <= i < len(rolls) and rolls[i] = v is at least r - 1.
    Preconditions: len(rolls) >= 1; 1 <= k <= 100000; len(rolls) <= 100000; for every i with 0 <= i < len(rolls), 1 <= rolls[i] <= k. -/
  theorem spec_15 (rolls : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val) :
      ∃ r : Std.I64,
        Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
          ∀ v : ℤ, 1 ≤ v → v ≤ k.val → r.val - 1 ≤ (occurrences rolls.val v : ℤ) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (rolls : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ rolls.val.length) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hlen2 : rolls.val.length ≤ 100000) (hvals : ValuesIn k.val rolls.val), ∃ r : Std.I64,
          Aegis.ShortestSequence.shortest_sequence rolls k = ok r ∧
            ∀ v : ℤ, 1 ≤ v → v ≤ k.val → r.val - 1 ≤ (occurrences rolls.val v : ℤ)) := by
    sorry

  end AegisSpec.ShortestSequence
