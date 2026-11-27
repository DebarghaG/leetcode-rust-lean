import Aegis.DeckRevealedIncreasing.Code.Funs

/-!
# Specifications of `Aegis.DeckRevealedIncreasing.deck_revealed_increasing`

LeetCode problem `reveal-cards-in-increasing-order`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DeckRevealedIncreasing

def reveal {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => x :: reveal (rest ++ [y])
  termination_by l => l.length

def vals (l : List I64) : List Int := l.map (fun x => x.val)

def sortedVals (deck : Slice I64) : List Int := (vals deck.val).mergeSort

def revealPositions (n : Nat) : List Nat := reveal (List.range n)

/-- Whenever the function returns a result r, let s be the sequence obtained by sorting all entries of deck in nondecreasing order. Then len(r) = len(deck) and RevealSeq(r) = s, where for any sequence a, RevealSeq(a) is defined by: RevealSeq([])=[]; RevealSeq([x])=[x]; and for m=len(a)>=2, RevealSeq(a) = [a[0]] concatenated with RevealSeq([a[2], a[3], ..., a[m-1], a[1]]). Equivalently, for every k with 0 <= k < len(deck), the k-th card revealed by the process starting from initial deck r (0-indexed) is the k-th smallest entry of deck.
  Preconditions: 1 <= len(deck) <= 1000; every deck[i] is an integer with 1 <= deck[i] <= 1000000; and all entries of deck are pairwise distinct (for all i,j with 0 <= i < j < len(deck), deck[i] != deck[j]). -/
theorem spec_1 (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r) :
    r.val.length = deck.val.length ∧ reveal (vals r.val) = sortedVals deck := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r), r.val.length = deck.val.length ∧ reveal (vals r.val) = sortedVals deck) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access outside the input or output bounds) for every input satisfying the preconditions.
  Preconditions: 1 <= len(deck) <= 1000; every deck[i] is an integer with 1 <= deck[i] <= 1000000; and all entries of deck are pairwise distinct (for all i,j with 0 <= i < j < len(deck), deck[i] != deck[j]). -/
theorem spec_2 (deck : Slice I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val) :
    ∃ r : alloc.vec.Vec I64, Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (deck : Slice I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val), ∃ r : alloc.vec.Vec I64, Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is a permutation of deck: for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(deck) and deck[j] = v. In particular, because the deck entries are distinct, each value deck[j] occurs exactly once in r and no other value occurs.
  Preconditions: 1 <= len(deck) <= 1000; every deck[i] is an integer with 1 <= deck[i] <= 1000000; and all entries of deck are pairwise distinct (for all i,j with 0 <= i < j < len(deck), deck[i] != deck[j]). -/
theorem spec_3 (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r) :
    ∀ v : Int, (vals r.val).count v = (vals deck.val).count v := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r), ∀ v : Int, (vals r.val).count v = (vals deck.val).count v) := by
  sorry

/-- Whenever the function returns a result r, let q be the sequence obtained by applying the reveal process to r (repeatedly: record the first element, remove it, and if elements remain move the new first element to the end). Then q is strictly increasing: for every k with 0 <= k and k+1 < len(q), q[k] < q[k+1].
  Preconditions: 1 <= len(deck) <= 1000; every deck[i] is an integer with 1 <= deck[i] <= 1000000; and all entries of deck are pairwise distinct (for all i,j with 0 <= i < j < len(deck), deck[i] != deck[j]). -/
theorem spec_4 (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r) :
    ∀ (k : Nat) (hk : k + 1 < (reveal (vals r.val)).length),
      (reveal (vals r.val)).get ⟨k, by omega⟩ <
        (reveal (vals r.val)).get ⟨k + 1, by omega⟩ := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r), ∀ (k : Nat) (hk : k + 1 < (reveal (vals r.val)).length),
      (reveal (vals r.val)).get ⟨k, by omega⟩ <
        (reveal (vals r.val)).get ⟨k + 1, by omega⟩) := by
  sorry

/-- Whenever the function returns a result r, r is a permutation of deck; the reveal process applied to r (repeatedly: record the first element, remove it, and if elements remain move the new first element to the end) yields exactly the nondecreasing sorted list s of deck entries; and for every sequence r' with len(r') = len(deck) that is a permutation of deck and whose reveal process yields s, we have r' = r.
  Preconditions: 1 <= len(deck) <= 1000; every deck[i] is an integer with 1 <= deck[i] <= 1000000; and all entries of deck are pairwise distinct (for all i,j with 0 <= i < j < len(deck), deck[i] != deck[j]). -/
theorem spec_5 (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r) :
    (∀ v : Int, (vals r.val).count v = (vals deck.val).count v) ∧
      reveal (vals r.val) = sortedVals deck ∧
      (∀ (r' : alloc.vec.Vec I64), r'.val.length = deck.val.length →
        (∀ v : Int, (vals r'.val).count v = (vals deck.val).count v) →
        reveal (vals r'.val) = sortedVals deck → r' = r) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r), (∀ v : Int, (vals r.val).count v = (vals deck.val).count v) ∧
      reveal (vals r.val) = sortedVals deck ∧
      (∀ (r' : alloc.vec.Vec I64), r'.val.length = deck.val.length →
        (∀ v : Int, (vals r'.val).count v = (vals deck.val).count v) →
        reveal (vals r'.val) = sortedVals deck → r' = r)) := by
  sorry

/-- Let n = len(deck). Let P_n be the sequence of positions produced by running the same move-to-bottom process on the list [0,1,...,n-1]: start with the queue [0,1,...,n-1]; repeatedly record the first element of the queue and remove it, and if the queue is nonempty then move its new first element to the end; P_n is the recorded sequence of length n. Let s be the nondecreasing sorted list of deck entries. Whenever the function returns a result r, len(r) = n and for every k with 0 <= k < n, r[P_n[k]] = s[k].
  Preconditions: 1 <= len(deck) <= 1000; every deck[i] is an integer with 1 <= deck[i] <= 1000000; and all entries of deck are pairwise distinct (for all i,j with 0 <= i < j < len(deck), deck[i] != deck[j]). -/
theorem spec_6 (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r) :
    r.val.length = deck.val.length ∧
      (∀ (k pk : Nat), k < deck.val.length →
        (revealPositions deck.val.length)[k]? = some pk →
        Option.map (fun x : I64 => x.val) (r.val[pk]?) = (sortedVals deck)[k]?) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (deck : Slice I64) (r : alloc.vec.Vec I64)
    (hlen_lower : 1 ≤ deck.val.length)
    (hlen_upper : deck.val.length ≤ 1000)
    (hentries : ∀ (i : Nat) (hi : i < deck.val.length),
      1 ≤ (deck.val[i]).val ∧ (deck.val[i]).val ≤ 1000000)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < deck.val.length),
      (deck.val.get ⟨i, by omega⟩).val ≠ (deck.val.get ⟨j, by omega⟩).val)
    (hr : Aegis.DeckRevealedIncreasing.deck_revealed_increasing deck = ok r), r.val.length = deck.val.length ∧
      (∀ (k pk : Nat), k < deck.val.length →
        (revealPositions deck.val.length)[k]? = some pk →
        Option.map (fun x : I64 => x.val) (r.val[pk]?) = (sortedVals deck)[k]?)) := by
  sorry

end AegisSpec.DeckRevealedIncreasing
