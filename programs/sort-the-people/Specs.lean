import Aegis.SortPeople.Code.Funs

/-!
# Specifications of `Aegis.SortPeople.sort_people`

LeetCode problem `sort-the-people`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SortPeople

  open Aegis.SortPeople (sort_people)

  def isLetterByte (b : U8) : Prop :=
    (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122)

  def isLetterBytes (bs : List U8) : Prop :=
    ∀ b ∈ bs, isLetterByte b

  def heightAt (heights : List I64) {n : ℕ} (hlen : heights.length = n) (j : Fin n) : ℤ :=
    (heights.get ⟨j.1, by omega⟩).val

  def countAbove (heights : List I64) (v : ℤ) : ℕ :=
    (heights.filter (fun x => v < x.val)).length

  def countOcc (l : List (alloc.vec.Vec U8)) (s : List U8) : ℕ :=
    (l.filter (fun v => v.val = s)).length

  def countOccPrefix (l : List (alloc.vec.Vec U8)) (k : ℕ) (s : List U8) : ℕ :=
    countOcc (l.take k) s

  /-- Whenever sort_people(names, heights) returns a result r, let n = len(names). Then len(r) = n, and there exists a sequence p of length n that is a permutation of {0,1,...,n-1} such that for every k with 0 <= k < n, r[k] = names[p[k]], and for every k with 0 <= k < n-1, heights[p[k]] > heights[p[k+1]].
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_1 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        r.val.length = names.val.length ∧
        ∃ (p : Fin names.val.length → Fin names.val.length),
          Function.Bijective p ∧
          r.val = (List.finRange names.val.length).map (fun k => names.val.get (p k)) ∧
          (∀ (k : ℕ) (hk : k + 1 < names.val.length),
            heightAt heights.val hlen (p ⟨k, by omega⟩) >
              heightAt heights.val hlen (p ⟨k + 1, hk⟩)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          r.val.length = names.val.length ∧
          ∃ (p : Fin names.val.length → Fin names.val.length),
            Function.Bijective p ∧
            r.val = (List.finRange names.val.length).map (fun k => names.val.get (p k)) ∧
            (∀ (k : ℕ) (hk : k + 1 < names.val.length),
              heightAt heights.val hlen (p ⟨k, by omega⟩) >
                heightAt heights.val hlen (p ⟨k + 1, hk⟩))) := by
    sorry

  /-- sort_people(names, heights) returns a result r; the call does not fail (no overflow, panic, or out-of-bounds failure).
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_2 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∃ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∃ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r) := by
    sorry

  /-- Whenever sort_people(names, heights) returns a result r, len(r) = len(names).
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_3 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        r.val.length = names.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          r.val.length = names.val.length) := by
    sorry

  /-- Whenever sort_people(names, heights) returns a result r, for every byte sequence s, the number of indices k with 0 <= k < len(r) and r[k] = s equals the number of indices i with 0 <= i < len(names) and names[i] = s.
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_4 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        ∀ (s : List U8), countOcc r.val s = countOcc names.val s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          ∀ (s : List U8), countOcc r.val s = countOcc names.val s) := by
    sorry

  /-- Whenever sort_people(names, heights) returns a result r, len(r) = len(names) and for every k with 0 <= k < len(names), there exists an index j with 0 <= j < len(names) such that r[k] = names[j] and the number of indices t with 0 <= t < len(names) and heights[t] > heights[j] is exactly k.
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_5 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        r.val.length = names.val.length ∧
        ∀ (k : Fin r.val.length), ∃ (j : Fin names.val.length),
          r.val.get k = names.val.get j ∧
          countAbove heights.val (heightAt heights.val hlen j) = k.1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          r.val.length = names.val.length ∧
          ∀ (k : Fin r.val.length), ∃ (j : Fin names.val.length),
            r.val.get k = names.val.get j ∧
            countAbove heights.val (heightAt heights.val hlen j) = k.1) := by
    sorry

  /-- Whenever sort_people(names, heights) returns a result r, len(r) = len(names) and for every k with 1 <= k <= len(names) and every byte sequence s, the number of indices q with 0 <= q < k and r[q] = s equals the number of indices j with 0 <= j < len(names), names[j] = s, and the number of indices t with 0 <= t < len(names) and heights[t] > heights[j] is less than k.
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_6 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        r.val.length = names.val.length ∧
        ∀ (k : ℕ), 1 ≤ k → k ≤ names.val.length → ∀ (s : List U8),
          countOccPrefix r.val k s =
            ((List.finRange names.val.length).filter
              (fun j => (names.val.get j).val = s ∧
                countAbove heights.val (heightAt heights.val hlen j) < k)).length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          r.val.length = names.val.length ∧
          ∀ (k : ℕ), 1 ≤ k → k ≤ names.val.length → ∀ (s : List U8),
            countOccPrefix r.val k s =
              ((List.finRange names.val.length).filter
                (fun j => (names.val.get j).val = s ∧
                  countAbove heights.val (heightAt heights.val hlen j) < k)).length) := by
    sorry

  /-- Whenever sort_people(names, heights) returns a result r, for every q with 0 <= q < len(r), 1 <= len(r[q]) <= 20.
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_7 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        ∀ (q : Fin r.val.length),
          1 ≤ (r.val.get q).val.length ∧ (r.val.get q).val.length ≤ 20 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          ∀ (q : Fin r.val.length),
            1 ≤ (r.val.get q).val.length ∧ (r.val.get q).val.length ≤ 20) := by
    sorry

  /-- Whenever sort_people(names, heights) returns a result r, for every q with 0 <= q < len(r) and every byte position b with 0 <= b < len(r[q]), the byte value r[q][b] is either in 65..90 or in 97..122.
    Preconditions: Let n = len(names). The following hold: len(heights) = n; 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= len(names[i]) <= 20, every byte of names[i] is an ASCII code of an English letter (65..90 or 97..122), and 1 <= heights[i] <= 100000; for every i and j with 0 <= i < j < n, heights[i] != heights[j]. -/
  theorem spec_8 (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
      (hlen : heights.val.length = names.val.length)
      (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
      (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
          isLetterBytes (names.val[i]'hi).val)
      (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
        1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
      (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
        i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩) :
      ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
        ∀ (q : Fin r.val.length) (b : Fin (r.val.get q).val.length),
          isLetterByte ((r.val.get q).val.get b) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (heights : Slice I64)
        (hlen : heights.val.length = names.val.length)
        (hn_pos : 1 ≤ names.val.length) (hn_le : names.val.length ≤ 1000)
        (hnames : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ (names.val[i]'hi).val.length ∧ (names.val[i]'hi).val.length ≤ 20 ∧
            isLetterBytes (names.val[i]'hi).val)
        (hheights : ∀ (i : ℕ) (hi : i < names.val.length),
          1 ≤ heightAt heights.val hlen ⟨i, hi⟩ ∧ heightAt heights.val hlen ⟨i, hi⟩ ≤ 100000)
        (hdistinct : ∀ (i j : ℕ) (hi : i < names.val.length) (hj : j < names.val.length),
          i < j → heightAt heights.val hlen ⟨i, hi⟩ ≠ heightAt heights.val hlen ⟨j, hj⟩), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)), sort_people names heights = ok r →
          ∀ (q : Fin r.val.length) (b : Fin (r.val.get q).val.length),
            isLetterByte ((r.val.get q).val.get b)) := by
    sorry

  end AegisSpec.SortPeople
