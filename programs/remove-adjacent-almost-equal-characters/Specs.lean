import Aegis.RemoveAlmostEqualCharacters.Code.Funs

/-!
# Specifications of `Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters`

LeetCode problem `remove-adjacent-almost-equal-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RemoveAlmostEqualCharacters

  def isLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def allLower (l : List Std.U8) : Prop := ∀ b ∈ l, isLowerByte b

  def almostEqual (a b : Std.U8) : Prop := a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1

  def almostEqualDecide (a b : Std.U8) : Bool :=
    decide (a.val ≤ b.val + 1) && decide (b.val ≤ a.val + 1)

  def adjacentPairs (l : List Std.U8) : List (Std.U8 × Std.U8) := l.zip l.tail

  def noAdjacentAlmostEqual (l : List Std.U8) : Prop :=
    ∀ p ∈ adjacentPairs l, ¬ almostEqual p.1 p.2

  def allAdjacentAlmostEqual (l : List Std.U8) : Prop :=
    ∀ p ∈ adjacentPairs l, almostEqual p.1 p.2

  def adjacencyPattern (l : List Std.U8) : List Bool :=
    (adjacentPairs l).map (fun p => almostEqualDecide p.1 p.2)

  def mismatches (w t : List Std.U8) : Nat :=
    (List.zipWith (fun a b => if a = b then 0 else 1) w t).sum

  def PointwiseImage (w t : List Std.U8) (f : Int → Int) : Prop :=
    t.length = w.length ∧ ∀ p ∈ w.zip t, (p.2.val : Int) = f (p.1.val : Int)

  def admissibleRewrite (w t : List Std.U8) : Prop :=
    t.length = w.length ∧ allLower t ∧ noAdjacentAlmostEqual t

  def IsMinChanges (w : List Std.U8) (c : Int) : Prop :=
    (∃ t, admissibleRewrite w t ∧ (mismatches w t : Int) = c) ∧
      ∀ t, admissibleRewrite w t → c ≤ (mismatches w t : Int)

  def edgePresent (w : List Std.U8) (j : Nat) : Bool := (adjacencyPattern w).getD j false

  def IsVertexCover (w : List Std.U8) (S : Finset Nat) : Prop :=
    S ⊆ Finset.range w.length ∧ ∀ j : Nat, edgePresent w j = true → j ∈ S ∨ j + 1 ∈ S

  def SameAdjacencyPattern (w v : List Std.U8) : Prop :=
    ∀ j : Nat, edgePresent w j = edgePresent v j

  def greedyCount : List Std.U8 → Nat
    | [] => 0
    | [_] => 0
    | a :: b :: rest => if almostEqualDecide a b then greedyCount rest + 1
                        else greedyCount (b :: rest)
  termination_by l => l.length
  decreasing_by all_goals simp_wf

  def componentSumAux : List Bool → Nat → Nat → Nat
    | [], cur, acc => acc + (cur + 1) / 2
    | true :: bs, cur, acc => componentSumAux bs (cur + 1) acc
    | false :: bs, cur, acc => componentSumAux bs 0 (acc + (cur + 1) / 2)

  def componentSum (w : List Std.U8) : Nat := componentSumAux (adjacencyPattern w) 0 0

  def validInput (w : List Std.U8) : Prop := 1 ≤ w.length ∧ w.length ≤ 100 ∧ allLower w

  /-- The function returns a result r (it does not fail). r is the minimum, over all byte arrays t of length n such that every byte of t is the ASCII code of a lowercase English letter and for every j with 0 <= j < n-1 the letters t[j] and t[j+1] are not almost-equal, of the number of indices i with 0 <= i < n and t[i] != word[i]. Here two lowercase letters are almost-equal exactly when they are equal or their alphabet positions differ by 1.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_1 (word : Slice Std.U8) (hpre : validInput word.val) :
      ∃ r : I64,
        Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r ∧
          IsMinChanges word.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice Std.U8) (hpre : validInput word.val), ∃ r : I64,
          Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r ∧
            IsMinChanges word.val r.val) := by
    sorry

  /-- For every input word satisfying the preconditions, the function returns a result r; it never fails, panics, or overflows.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_2 (word : Slice Std.U8) (hpre : validInput word.val) :
      ∃ r : I64,
        Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice Std.U8) (hpre : validInput word.val), ∃ r : I64,
          Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_3 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= floor(n / 2), where n = len(word) and floor(n / 2) is integer division of n by 2.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_4 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      r.val ≤ ((word.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), r.val ≤ ((word.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every j with 0 <= j < n-1, word[j] and word[j+1] are not almost-equal.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_5 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      r.val = 0 ↔ noAdjacentAlmostEqual word.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), r.val = 0 ↔ noAdjacentAlmostEqual word.val) := by
    sorry

  /-- Whenever the function returns a result r, r = floor(n / 2), with integer division by 2.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). Also, for every j with 0 <= j < n-1, word[j] and word[j+1] are almost-equal. -/
  theorem spec_6 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hall : allAdjacentAlmostEqual word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      r.val = ((word.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hall : allAdjacentAlmostEqual word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), r.val = ((word.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Let rev be the byte array of length n defined by rev[i] = word[n-1-i] for 0 <= i < n. Whenever the function returns r on word and returns r' on rev, r = r'.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_7 (word rev : Slice Std.U8) (r r' : I64) (hpre : validInput word.val)
      (hrev : rev.val = word.val.reverse)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
      (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters rev = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word rev : Slice Std.U8) (r r' : I64) (hpre : validInput word.val)
        (hrev : rev.val = word.val.reverse)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
        (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters rev = ok r'), r = r') := by
    sorry

  /-- Let alt be the byte array of length n defined by alt[i] = 122 - (word[i] - 97) for 0 <= i < n, i.e. each letter is replaced by its mirror in the alphabet (a<->z, b<->y, ..., m<->n). Whenever the function returns r on word and returns r' on alt, r = r'.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_8 (word alt : Slice Std.U8) (r r' : I64) (hpre : validInput word.val)
      (halt : PointwiseImage word.val alt.val (fun x => 122 - (x - 97)))
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
      (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters alt = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word alt : Slice Std.U8) (r r' : I64) (hpre : validInput word.val)
        (halt : PointwiseImage word.val alt.val (fun x => 122 - (x - 97)))
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
        (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters alt = ok r'), r = r') := by
    sorry

  /-- Let shift be the byte array of length n defined by shift[i] = word[i] + d for 0 <= i < n. Whenever the function returns r on word and returns r' on shift, r = r'.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). There is an integer d such that for every i with 0 <= i < n, the byte word[i] + d is still the ASCII code of a lowercase English letter. -/
  theorem spec_9 (word shift : Slice Std.U8) (r r' : I64) (d : Int)
      (hpre : validInput word.val)
      (hshift : PointwiseImage word.val shift.val (fun x => x + d))
      (hlower : allLower shift.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
      (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters shift = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word shift : Slice Std.U8) (r r' : I64) (d : Int)
        (hpre : validInput word.val)
        (hshift : PointwiseImage word.val shift.val (fun x => x + d))
        (hlower : allLower shift.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
        (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters shift = ok r'), r = r') := by
    sorry

  /-- For every k with 1 <= k <= n, let pre_k be the slice (word[0], ..., word[k-1]). Whenever the function returns r on word and r_k on pre_k, r_k <= r.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_10 (word pre : Slice Std.U8) (r r_k : I64) (k : Nat)
      (hpre : validInput word.val) (hk : 1 ≤ k ∧ k ≤ word.val.length)
      (hprek : pre.val = word.val.take k)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
      (hrk : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters pre = ok r_k) :
      r_k.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word pre : Slice Std.U8) (r r_k : I64) (k : Nat)
        (hpre : validInput word.val) (hk : 1 ≤ k ∧ k ≤ word.val.length)
        (hprek : pre.val = word.val.take k)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
        (hrk : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters pre = ok r_k), r_k.val ≤ r.val) := by
    sorry

  /-- For every k with 1 <= k <= n, let pre_k be the slice (word[0], ..., word[k-1]). Whenever the function returns r on word and r_k on pre_k, r <= r_k + (n - k).
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_11 (word pre : Slice Std.U8) (r r_k : I64) (k : Nat)
      (hpre : validInput word.val) (hk : 1 ≤ k ∧ k ≤ word.val.length)
      (hprek : pre.val = word.val.take k)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
      (hrk : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters pre = ok r_k) :
      r.val ≤ r_k.val + ((word.val.length - k : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word pre : Slice Std.U8) (r r_k : I64) (k : Nat)
        (hpre : validInput word.val) (hk : 1 ≤ k ∧ k ≤ word.val.length)
        (hprek : pre.val = word.val.take k)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
        (hrk : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters pre = ok r_k), r.val ≤ r_k.val + ((word.val.length - k : Nat) : Int)) := by
    sorry

  /-- Let G be the undirected graph with vertex set {0, 1, ..., n-1} and with an edge between j and j+1 exactly when word[j] and word[j+1] are almost-equal, for 0 <= j < n-1; there are no other edges. Whenever the function returns a result r, r is the minimum cardinality of a subset S of {0, 1, ..., n-1} such that every edge of G has at least one endpoint in S. Equivalently, r is the size of a minimum vertex cover of G.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_12 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      ∃ S : Finset Nat,
        IsVertexCover word.val S ∧ r.val = (S.card : Int) ∧
          ∀ S' : Finset Nat, IsVertexCover word.val S' → S.card ≤ S'.card := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), ∃ S : Finset Nat,
          IsVertexCover word.val S ∧ r.val = (S.card : Int) ∧
            ∀ S' : Finset Nat, IsVertexCover word.val S' → S.card ≤ S'.card) := by
    sorry

  /-- Let G be the undirected graph on {0, 1, ..., n-1} with an edge between j and j+1 exactly when word[j] and word[j+1] are almost-equal. Whenever the function returns a result r, r equals the sum, over all connected components C of G, of floor(|V(C)| / 2), where |V(C)| is the number of vertices in C and division is integer division by 2.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_13 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      r.val = ((componentSum word.val : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), r.val = ((componentSum word.val : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a byte array t of length n such that every byte of t is a lowercase English letter, for every j with 0 <= j < n-1 the letters t[j] and t[j+1] are not almost-equal, and exactly r indices i with 0 <= i < n satisfy t[i] != word[i].
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_14 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      ∃ t : List Std.U8,
        admissibleRewrite word.val t ∧ (mismatches word.val t : Int) = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), ∃ t : List Std.U8,
          admissibleRewrite word.val t ∧ (mismatches word.val t : Int) = r.val) := by
    sorry

  /-- Define a left-to-right scan with i = 0 and c = 0: while i + 1 < n, if word[i] and word[i+1] are almost-equal then increment c and set i := i + 2, otherwise set i := i + 1. Whenever the function returns a result r, r = c. Here two lowercase letters are almost-equal exactly when equal or their alphabet positions differ by 1.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_15 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      r.val = ((greedyCount word.val : Nat) : Int) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), r.val = ((greedyCount word.val : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns r on word and r' on v, r = r'. That is, the answer depends only on the pattern of adjacent almost-equal pairs, not on the actual letters.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). Also let v be a byte array of length n, all of whose bytes are lowercase English letters, such that for every j with 0 <= j < n-1, word[j] and word[j+1] are almost-equal if and only if v[j] and v[j+1] are almost-equal. -/
  theorem spec_16 (word v : Slice Std.U8) (r r' : I64) (hpre : validInput word.val)
      (hlen : v.val.length = word.val.length) (hlower : allLower v.val)
      (hpat : SameAdjacencyPattern word.val v.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
      (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters v = ok r') :
      r = r' := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (word v : Slice Std.U8) (r r' : I64) (hpre : validInput word.val)
        (hlen : v.val.length = word.val.length) (hlower : allLower v.val)
        (hpat : SameAdjacencyPattern word.val v.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r)
        (hr' : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters v = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns a result r, for every byte array t of length n such that every byte of t is a lowercase English letter and for every j with 0 <= j < n-1 the letters t[j] and t[j+1] are not almost-equal, the number of indices i with 0 <= i < n and t[i] != word[i] is at least r.
    Preconditions: Let n = len(word). The slice word has 1 <= n <= 100 and every byte of word is the ASCII code of a lowercase English letter ('a' through 'z'). -/
  theorem spec_17 (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
      (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r) :
      ∀ t : List Std.U8, admissibleRewrite word.val t →
        r.val ≤ (mismatches word.val t : Int) := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (word : Slice Std.U8) (r : I64) (hpre : validInput word.val)
        (hr : Aegis.RemoveAlmostEqualCharacters.remove_almost_equal_characters word = ok r), ∀ t : List Std.U8, admissibleRewrite word.val t →
          r.val ≤ (mismatches word.val t : Int)) := by
    sorry

  end AegisSpec.RemoveAlmostEqualCharacters
