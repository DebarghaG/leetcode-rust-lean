import Aegis.InterchangeableRectangles.Code.Funs

/-!
# Specifications of `Aegis.InterchangeableRectangles.interchangeable_rectangles`

LeetCode problem `number-of-pairs-of-interchangeable-rectangles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.InterchangeableRectangles

  open Aegis.InterchangeableRectangles

  def sameRatio (w h w' h' : Int) : Prop :=
    w * h' = w' * h

  instance sameRatio.decidable (w h w' h' : Int) : Decidable (sameRatio w h w' h') :=
    inferInstanceAs (Decidable (w * h' = w' * h))

  def ValidInput (rectangles : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ rectangles.val.length ∧ rectangles.val.length ≤ 100000 ∧
      ∀ v ∈ rectangles.val, v.val.length = 2 ∧ ∀ x ∈ v.val, 1 ≤ x.val ∧ x.val ≤ 100000

  def rectPair (v : alloc.vec.Vec Std.I64) : Int × Int :=
    match v.val with
    | w :: h :: _ => (w.val, h.val)
    | _ => (0, 0)

  def rectPairs (rectangles : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
    rectangles.val.map rectPair

  def wAt (rectangles : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((rectPairs rectangles).getD i (0, 0)).1

  def hAt (rectangles : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((rectPairs rectangles).getD i (0, 0)).2

  def totalPairs (n : Nat) : Nat :=
    n * (n - 1) / 2

  def numEqualPairs (rectangles : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    ((Finset.range rectangles.val.length ×ˢ Finset.range rectangles.val.length).filter
        (fun p : Nat × Nat =>
          p.1 < p.2 ∧
            sameRatio (wAt rectangles p.1) (hAt rectangles p.1) (wAt rectangles p.2)
              (hAt rectangles p.2))).card

  def numSameRatio (rectangles : Slice (alloc.vec.Vec Std.I64)) (W H : Int) : Nat :=
    ((Finset.range rectangles.val.length).filter
        (fun i => sameRatio (wAt rectangles i) (hAt rectangles i) W H)).card

  /-- The function returns a result r, and r is the number of pairs of indices (i,j) with 0 <= i < j < n such that w_i/h_i = w_j/h_j as rational numbers; equivalently, such that w_i*h_j = w_j*h_i. Each unordered pair is counted exactly once.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. For 0 <= i < n write w_i = rectangles[i][0] and h_i = rectangles[i][1]. -/
  theorem spec_1
      (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hvalid : ValidInput rectangles) :
      ∃ r : Std.I64,
        interchangeable_rectangles rectangles = ok r ∧
          r.val = (numEqualPairs rectangles : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hvalid : ValidInput rectangles), ∃ r : Std.I64,
          interchangeable_rectangles rectangles = ok r ∧
            r.val = (numEqualPairs rectangles : Int)) := by
    sorry

  /-- Under the preconditions, the function returns a result r; it does not panic, overflow, or otherwise fail.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. -/
  theorem spec_2
      (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hvalid : ValidInput rectangles) :
      ∃ r : Std.I64, interchangeable_rectangles rectangles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hvalid : ValidInput rectangles), ∃ r : Std.I64, interchangeable_rectangles rectangles = ok r) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, 0 <= r.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. -/
  theorem spec_3
      (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hvalid : ValidInput rectangles) :
      ∀ r : Std.I64, interchangeable_rectangles rectangles = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hvalid : ValidInput rectangles), ∀ r : Std.I64, interchangeable_rectangles rectangles = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r <= n*(n-1)/2.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. -/
  theorem spec_4
      (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hvalid : ValidInput rectangles) (n : Nat) (hn : n = rectangles.val.length) :
      ∀ r : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          r.val ≤ ((totalPairs n : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hvalid : ValidInput rectangles) (n : Nat) (hn : n = rectangles.val.length), ∀ r : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            r.val ≤ ((totalPairs n : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r = 0 if and only if for every pair of indices i,j with 0 <= i < j < n, w_i*h_j != w_j*h_i.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. For 0 <= i < n write w_i = rectangles[i][0] and h_i = rectangles[i][1]. -/
  theorem spec_5
      (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hvalid : ValidInput rectangles) (n : Nat) (hn : n = rectangles.val.length) :
      ∀ r : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          (r.val = 0 ↔
            ∀ i j : Nat,
              i < j → j < n →
                ¬ sameRatio (wAt rectangles i) (hAt rectangles i) (wAt rectangles j)
                    (hAt rectangles j)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hvalid : ValidInput rectangles) (n : Nat) (hn : n = rectangles.val.length), ∀ r : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            (r.val = 0 ↔
              ∀ i j : Nat,
                i < j → j < n →
                  ¬ sameRatio (wAt rectangles i) (hAt rectangles i) (wAt rectangles j)
                      (hAt rectangles j))) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r = n*(n-1)/2 if and only if for every pair of indices i,j with 0 <= i < j < n, w_i*h_j = w_j*h_i.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. For 0 <= i < n write w_i = rectangles[i][0] and h_i = rectangles[i][1]. -/
  theorem spec_6
      (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hvalid : ValidInput rectangles) (n : Nat) (hn : n = rectangles.val.length) :
      ∀ r : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          (r.val = ((totalPairs n : Nat) : Int) ↔
            ∀ i j : Nat,
              i < j → j < n →
                sameRatio (wAt rectangles i) (hAt rectangles i) (wAt rectangles j)
                  (hAt rectangles j)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hvalid : ValidInput rectangles) (n : Nat) (hn : n = rectangles.val.length), ∀ r : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            (r.val = ((totalPairs n : Nat) : Int) ↔
              ∀ i j : Nat,
                i < j → j < n →
                  sameRatio (wAt rectangles i) (hAt rectangles i) (wAt rectangles j)
                    (hAt rectangles j))) := by
    sorry

  /-- Let rectangles' be any other valid input of the same length n for which there is a bijection p from {0,...,n-1} to {0,...,n-1} such that rectangles'[i][0] = rectangles[p(i)][0] and rectangles'[i][1] = rectangles[p(i)][1] for every i. If the function returns r on rectangles and r' on rectangles', then r = r'.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. -/
  theorem spec_7
      (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (n : Nat) (hn : n = rectangles.val.length) (hn' : rectangles'.val.length = n)
      (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
      (p : Equiv.Perm (Fin n))
      (hp : ∀ i : Fin n,
        wAt rectangles' i.val = wAt rectangles (p i).val ∧
          hAt rectangles' i.val = hAt rectangles (p i).val) :
      ∀ r r' : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          interchangeable_rectangles rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (n : Nat) (hn : n = rectangles.val.length) (hn' : rectangles'.val.length = n)
        (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
        (p : Equiv.Perm (Fin n))
        (hp : ∀ i : Fin n,
          wAt rectangles' i.val = wAt rectangles (p i).val ∧
            hAt rectangles' i.val = hAt rectangles (p i).val), ∀ r r' : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            interchangeable_rectangles rectangles' = ok r' → r = r') := by
    sorry

  /-- Let rectangles' be another valid input of the same length n, with entries w'_i,h'_i. Suppose that for all indices i,j with 0 <= i < j < n, w_i*h_j = w_j*h_i if and only if w'_i*h'_j = w'_j*h'_i. If the function returns r on rectangles and r' on rectangles', then r = r'.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. For 0 <= i < n write w_i = rectangles[i][0] and h_i = rectangles[i][1]. -/
  theorem spec_8
      (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (n : Nat) (hn : n = rectangles.val.length) (hn' : rectangles'.val.length = n)
      (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
      (hsame : ∀ i j : Nat,
        i < j → j < n →
          (sameRatio (wAt rectangles i) (hAt rectangles i) (wAt rectangles j)
              (hAt rectangles j) ↔
            sameRatio (wAt rectangles' i) (hAt rectangles' i) (wAt rectangles' j)
              (hAt rectangles' j))) :
      ∀ r r' : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          interchangeable_rectangles rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (n : Nat) (hn : n = rectangles.val.length) (hn' : rectangles'.val.length = n)
        (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
        (hsame : ∀ i j : Nat,
          i < j → j < n →
            (sameRatio (wAt rectangles i) (hAt rectangles i) (wAt rectangles j)
                (hAt rectangles j) ↔
              sameRatio (wAt rectangles' i) (hAt rectangles' i) (wAt rectangles' j)
                (hAt rectangles' j))), ∀ r r' : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            interchangeable_rectangles rectangles' = ok r' → r = r') := by
    sorry

  /-- Let rectangles' be the valid input of length n obtained from rectangles by replacing the k-th rectangle with (c*rectangles[k][0], c*rectangles[k][1]) and leaving all other entries unchanged. If the function returns r on rectangles and r' on rectangles', then r = r'.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. Let k satisfy 0 <= k < n, and let c be a positive integer (c >= 1) such that c*rectangles[k][0] <= 100000 and c*rectangles[k][1] <= 100000. -/
  theorem spec_9
      (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (n : Nat) (hn : n = rectangles.val.length) (hn' : rectangles'.val.length = n)
      (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
      (k : Nat) (hk : k < n) (c : Int) (hc : 1 ≤ c)
      (hwk : c * wAt rectangles k ≤ 100000) (hhk : c * hAt rectangles k ≤ 100000)
      (hk' : wAt rectangles' k = c * wAt rectangles k ∧
        hAt rectangles' k = c * hAt rectangles k)
      (hother : ∀ i : Nat, i < n → i ≠ k →
        wAt rectangles' i = wAt rectangles i ∧ hAt rectangles' i = hAt rectangles i) :
      ∀ r r' : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          interchangeable_rectangles rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (n : Nat) (hn : n = rectangles.val.length) (hn' : rectangles'.val.length = n)
        (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
        (k : Nat) (hk : k < n) (c : Int) (hc : 1 ≤ c)
        (hwk : c * wAt rectangles k ≤ 100000) (hhk : c * hAt rectangles k ≤ 100000)
        (hk' : wAt rectangles' k = c * wAt rectangles k ∧
          hAt rectangles' k = c * hAt rectangles k)
        (hother : ∀ i : Nat, i < n → i ≠ k →
          wAt rectangles' i = wAt rectangles i ∧ hAt rectangles' i = hAt rectangles i), ∀ r r' : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            interchangeable_rectangles rectangles' = ok r' → r = r') := by
    sorry

  /-- Let rectangles' be the valid input of length n+1 whose first n entries are exactly the entries of rectangles and whose last entry is (W,H). If the function returns r on rectangles and r' on rectangles', then r' = r + #{i | 0 <= i < n and w_i*H = W*h_i}.
    Preconditions: Let n = len(rectangles). Preconditions: 1 <= n <= 100000; for every i with 0 <= i < n, len(rectangles[i]) = 2 and 1 <= rectangles[i][0] <= 100000 and 1 <= rectangles[i][1] <= 100000. Additionally assume n <= 99999, and let W,H be integers with 1 <= W <= 100000 and 1 <= H <= 100000. For 0 <= i < n write w_i = rectangles[i][0] and h_i = rectangles[i][1]. -/
  theorem spec_10
      (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (n : Nat) (hn : n = rectangles.val.length) (hnle : n ≤ 99999)
      (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
      (W H : Int) (hW : 1 ≤ W) (hW' : W ≤ 100000) (hH : 1 ≤ H) (hH' : H ≤ 100000)
      (hlen' : rectangles'.val.length = n + 1)
      (hpre : ∀ i : Nat, i < n →
        wAt rectangles' i = wAt rectangles i ∧ hAt rectangles' i = hAt rectangles i)
      (hlast : wAt rectangles' n = W ∧ hAt rectangles' n = H) :
      ∀ r r' : Std.I64,
        interchangeable_rectangles rectangles = ok r →
          interchangeable_rectangles rectangles' = ok r' →
            r'.val = r.val + (numSameRatio rectangles W H : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (n : Nat) (hn : n = rectangles.val.length) (hnle : n ≤ 99999)
        (hvalid : ValidInput rectangles) (hvalid' : ValidInput rectangles')
        (W H : Int) (hW : 1 ≤ W) (hW' : W ≤ 100000) (hH : 1 ≤ H) (hH' : H ≤ 100000)
        (hlen' : rectangles'.val.length = n + 1)
        (hpre : ∀ i : Nat, i < n →
          wAt rectangles' i = wAt rectangles i ∧ hAt rectangles' i = hAt rectangles i)
        (hlast : wAt rectangles' n = W ∧ hAt rectangles' n = H), ∀ r r' : Std.I64,
          interchangeable_rectangles rectangles = ok r →
            interchangeable_rectangles rectangles' = ok r' →
              r'.val = r.val + (numSameRatio rectangles W H : Int)) := by
    sorry

  end AegisSpec.InterchangeableRectangles
