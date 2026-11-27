import Aegis.NumSimilarGroups.Code.Funs

/-!
# Specifications of `Aegis.NumSimilarGroups.num_similar_groups`

LeetCode problem `similar-string-groups`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumSimilarGroups

abbrev ByteString : Type := List Std.U8

def contents (strs : Slice (alloc.vec.Vec Std.U8)) : List ByteString :=
  strs.val.map (fun v => v.val)

def len (strs : Slice (alloc.vec.Vec Std.U8)) : Nat :=
  (contents strs).length

def sv (strs : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : ByteString :=
  (contents strs)[i]!

def similar (x y : ByteString) : Prop :=
  x.length = y.length ∧
    (x = y ∨
      ∃ p q : Nat,
        p < q ∧ q < x.length ∧
          y[p]? = x[q]? ∧ y[q]? = x[p]? ∧
            ∀ k : Nat, k < x.length → k ≠ p → k ≠ q → y[k]? = x[k]?)

def hamming (x y : ByteString) : Nat :=
  (List.range x.length).countP (fun k => decide (x[k]? ≠ y[k]?))

def anagram (s t : ByteString) : Prop :=
  ∀ c : Std.U8,
    (s.filter (fun b => decide (b = c))).length
      = (t.filter (fun b => decide (b = c))).length

def SameLen (strs : Slice (alloc.vec.Vec Std.U8)) (L : Nat) : Prop :=
  ∀ s ∈ contents strs, s.length = L

def Lowercase (strs : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ s ∈ contents strs, ∀ b ∈ s, 97 ≤ b.val ∧ b.val ≤ 122

def PairwiseAnagram (strs : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  ∀ s ∈ contents strs, ∀ t ∈ contents strs, anagram s t

def adjPos (vs : List ByteString) (i j : Nat) : Prop :=
  ∃ x y : ByteString, vs[i]? = some x ∧ vs[j]? = some y ∧ i ≠ j ∧ similar x y

def adjHam (vs : List ByteString) (i j : Nat) : Prop :=
  ∃ x y : ByteString,
    vs[i]? = some x ∧ vs[j]? = some y ∧ i ≠ j ∧
      (hamming x y = 0 ∨ hamming x y = 2)

def reach (adj : Nat → Nat → Prop) (i j : Nat) : Prop :=
  Relation.ReflTransGen adj i j

noncomputable def numComponents (n : Nat) (adj : Nat → Nat → Prop) : Nat := by
  classical
  exact ((Finset.range n).filter
    (fun i => ∀ j ∈ Finset.range n, reach adj j i → i ≤ j)).card

/-- Let G be the undirected graph with vertex set {0,1,...,len(strs)-1} in which two distinct vertices i and j are adjacent exactly when strs[i] and strs[j] are similar, where two strings x and y of equal length are similar iff x = y or there exist distinct positions p and q with 0 <= p < q < len(x), x[p] = y[q], x[q] = y[p], and x[k] = y[k] for every k with 0 <= k < len(x) and k not in {p,q}. Then the function returns a result r equal to the number of connected components of G; equivalently, r is the number of equivalence classes of the reflexive-transitive closure of the edge relation on the index set, i.e., the relation in which i and j are equivalent iff i = j or there is a finite path of edges from i to j.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_1 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∃ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r ∧
        r.val = (numComponents (len strs) (adjPos (contents strs)) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∃ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r ∧
        r.val = (numComponents (len strs) (adjPos (contents strs)) : Int)) := by
  sorry

/-- The function returns a result r; in particular, it does not panic, does not access an out-of-bounds index, and does not overflow 64-bit signed integer arithmetic.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_2 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∃ r : Std.I64, Aegis.NumSimilarGroups.num_similar_groups strs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∃ r : Std.I64, Aegis.NumSimilarGroups.num_similar_groups strs = ok r) := by
  sorry

/-- The returned value r satisfies r >= 1.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_3 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ r : Std.I64, Aegis.NumSimilarGroups.num_similar_groups strs = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ r : Std.I64, Aegis.NumSimilarGroups.num_similar_groups strs = ok r → 1 ≤ r.val) := by
  sorry

/-- The returned value r satisfies r <= len(strs).
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_4 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r → r.val ≤ (len strs : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r → r.val ≤ (len strs : Int)) := by
  sorry

/-- Let d be the number of distinct byte-vectors among strs[0],...,strs[len(strs)-1]. Then r <= d.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_5 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        r.val ≤ ((contents strs).dedup.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        r.val ≤ ((contents strs).dedup.length : Int)) := by
  sorry

/-- The function returns r = len(strs).
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams; and for every i,j with 0 <= i < j < len(strs), strs[i] and strs[j] are not similar, where similar means x = y or there exist distinct positions p<q with x[p]=y[q], x[q]=y[p], and x[k]=y[k] for all k not in {p,q}. -/
theorem spec_6 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs)
    (hdisj : ∀ i j : Nat, i < j → j < len strs → ¬ similar (sv strs i) (sv strs j)) :
    ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r → r.val = (len strs : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs)
    (hdisj : ∀ i j : Nat, i < j → j < len strs → ¬ similar (sv strs i) (sv strs j)), ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r → r.val = (len strs : Int)) := by
  sorry

/-- Let S be the set of distinct byte-vectors occurring among strs[0],...,strs[len(strs)-1]. Form the undirected graph H on S where two distinct values x and y are adjacent exactly when x and y are similar (x = y, or there exist distinct positions p<q with x[p]=y[q], x[q]=y[p], and x[k]=y[k] for all k not in {p,q}). Then r equals the number of connected components of H.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_7 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∃ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r ∧
        r.val =
          (numComponents (contents strs).dedup.length
            (adjPos (contents strs).dedup) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∃ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r ∧
        r.val =
          (numComponents (contents strs).dedup.length
            (adjPos (contents strs).dedup) : Int)) := by
  sorry

/-- If there exists an index c with 0 <= c < len(strs) such that strs[c] is similar to strs[j] for every j with 0 <= j < len(strs) and j != c (similar means identical or obtainable by one swap of two distinct positions), then r = 1.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_8 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        (∃ c : Nat, c < len strs ∧
          ∀ j : Nat, j < len strs → j ≠ c → similar (sv strs c) (sv strs j)) →
        r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        (∃ c : Nat, c < len strs ∧
          ∀ j : Nat, j < len strs → j ≠ c → similar (sv strs c) (sv strs j)) →
        r.val = 1) := by
  sorry

/-- The returned value r equals 1 if and only if for every two indices i,j with 0 <= i < len(strs) and 0 <= j < len(strs) there exists a finite sequence i = p0, p1, ..., pk = j with k >= 0 such that for every t with 0 <= t < k, strs[p_t] and strs[p_{t+1}] are similar (identical or obtainable by one swap of two distinct positions).
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_9 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        (r.val = 1 ↔
          ∀ i j : Nat, i < len strs → j < len strs →
            reach (adjPos (contents strs)) i j) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        (r.val = 1 ↔
          ∀ i j : Nat, i < len strs → j < len strs →
            reach (adjPos (contents strs)) i j)) := by
  sorry

/-- For every permutation π of the set {0,1,...,len(strs)-1}, the value returned by the function on the reordered list (strs[π(0)], strs[π(1)], ..., strs[π(len(strs)-1)]) is equal to r.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_10 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ (π : Equiv.Perm (Fin (len strs))) (strs' : Slice (alloc.vec.Vec Std.U8))
      (r : Std.I64),
      contents strs' = List.ofFn (fun i : Fin (len strs) => (contents strs).get (π i)) →
        Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
          Aegis.NumSimilarGroups.num_similar_groups strs' = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ (π : Equiv.Perm (Fin (len strs))) (strs' : Slice (alloc.vec.Vec Std.U8))
      (r : Std.I64),
      contents strs' = List.ofFn (fun i : Fin (len strs) => (contents strs).get (π i)) →
        Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
          Aegis.NumSimilarGroups.num_similar_groups strs' = ok r) := by
  sorry

/-- Let r be the value returned by the function on strs. Let strs' be the list obtained by appending one additional copy of strs[0] at the end of strs (so len(strs') = len(strs)+1 and strs'[len(strs)] = strs[0]). Then the value returned by the function on strs' equals r.
  Preconditions: 1 <= len(strs) <= 299; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_11 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn299 : len strs ≤ 299)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ (strs' : Slice (alloc.vec.Vec Std.U8)) (r : Std.I64),
      contents strs' = contents strs ++ [sv strs 0] →
        Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
          Aegis.NumSimilarGroups.num_similar_groups strs' = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn299 : len strs ≤ 299)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ (strs' : Slice (alloc.vec.Vec Std.U8)) (r : Std.I64),
      contents strs' = contents strs ++ [sv strs 0] →
        Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
          Aegis.NumSimilarGroups.num_similar_groups strs' = ok r) := by
  sorry

/-- Let r be the value returned by the function. Then r = len(strs) if and only if for every i,j with 0 <= i < j < len(strs), strs[i] and strs[j] are not similar (where two strings x and y of equal length are similar iff x = y or there exist distinct positions p<q with x[p]=y[q], x[q]=y[p], and x[k]=y[k] for every k not in {p,q}).
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_12 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        (r.val = (len strs : Int) ↔
          ∀ i j : Nat, i < j → j < len strs → ¬ similar (sv strs i) (sv strs j)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
        (r.val = (len strs : Int) ↔
          ∀ i j : Nat, i < j → j < len strs → ¬ similar (sv strs i) (sv strs j))) := by
  sorry

/-- Let r be the value returned by the function on strs. For every index i with 0 <= i < len(strs), let strs' be the list obtained by appending one additional copy of strs[i] at the end of strs (so len(strs')=len(strs)+1 and strs'[len(strs)]=strs[i]). Then the value returned by the function on strs' equals r.
  Preconditions: 1 <= len(strs) <= 299; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_13 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn299 : len strs ≤ 299)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∀ (i : Nat) (_hi : i < len strs) (strs' : Slice (alloc.vec.Vec Std.U8))
      (r : Std.I64),
      contents strs' = contents strs ++ [sv strs i] →
        Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
          Aegis.NumSimilarGroups.num_similar_groups strs' = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn299 : len strs ≤ 299)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∀ (i : Nat) (_hi : i < len strs) (strs' : Slice (alloc.vec.Vec Std.U8))
      (r : Std.I64),
      contents strs' = contents strs ++ [sv strs i] →
        Aegis.NumSimilarGroups.num_similar_groups strs = ok r →
          Aegis.NumSimilarGroups.num_similar_groups strs' = ok r) := by
  sorry

/-- Let H be the undirected graph with vertex set {0,1,...,len(strs)-1} in which two distinct vertices i and j are adjacent exactly when the Hamming distance between strs[i] and strs[j] (the number of positions k with 0 <= k < L and strs[i][k] != strs[j][k]) is either 0 or 2. Then the function returns the number of connected components of H.
  Preconditions: 1 <= len(strs) <= 300; there exists an integer L with 1 <= L <= 300 such that len(strs[i]) = L for every i with 0 <= i < len(strs); every byte of every strs[i] is a lowercase ASCII letter (97 <= byte <= 122); and for every i,j with 0 <= i < len(strs) and 0 <= j < len(strs), strs[i] and strs[j] are anagrams, i.e., for every byte value c the number of positions k with strs[i][k] = c equals the number of positions k with strs[j][k] = c. -/
theorem spec_14 (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs) :
    ∃ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r ∧
        r.val =
          (numComponents (len strs) (adjHam (contents strs)) : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hn1 : 1 ≤ len strs) (hn300 : len strs ≤ 300)
    (hL : ∃ L : Nat, 1 ≤ L ∧ L ≤ 300 ∧ SameLen strs L)
    (hlow : Lowercase strs) (hana : PairwiseAnagram strs), ∃ r : Std.I64,
      Aegis.NumSimilarGroups.num_similar_groups strs = ok r ∧
        r.val =
          (numComponents (len strs) (adjHam (contents strs)) : Int)) := by
  sorry

end AegisSpec.NumSimilarGroups
