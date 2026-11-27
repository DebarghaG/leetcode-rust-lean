import Aegis.MinCharacters.Code.Funs

/-!
# Specifications of `Aegis.MinCharacters.min_characters`

LeetCode problem `change-minimum-characters-to-satisfy-one-of-three-conditions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCharacters

def IsLowerByte (x : U8) : Prop := 97 ≤ x.val ∧ x.val ≤ 122

def AllLowerBytes (l : List U8) : Prop := ∀ x ∈ l, IsLowerByte x

def numDiffs (l₁ l₂ : List U8) : ℕ :=
  (l₁.zipWith (fun x y => if x = y then 0 else 1) l₂).sum

def changeCost (A' B' a b : List U8) : ℕ :=
  numDiffs A' a + numDiffs B' b

def AllLess (A' B' : List U8) : Prop := ∀ x ∈ A', ∀ y ∈ B', x.val < y.val

def AllEqual (l : List U8) : Prop := ∀ x ∈ l, ∀ y ∈ l, x = y

def AdmissiblePair (A' B' : List U8) : Prop :=
  AllLess A' B' ∨ AllLess B' A' ∨ (AllEqual A' ∧ AllEqual B')

def IsTargetPair (A' B' : List U8) (a b : Slice U8) : Prop :=
  A'.length = a.val.length ∧ B'.length = b.val.length ∧
    AllLowerBytes A' ∧ AllLowerBytes B'

def countGt (l : List U8) (k : ℤ) : ℕ :=
  (l.filter fun x => decide (k < (x.val : ℤ) - 97)).length

def countLe (l : List U8) (k : ℤ) : ℕ :=
  (l.filter fun x => decide ((x.val : ℤ) - 97 ≤ k)).length

def countOfByte (l : List U8) (y : U8) : ℕ :=
  (l.filter fun x => decide (x = y)).length

def countOfOffset (l : List U8) (k : ℕ) : ℕ :=
  (l.filter fun x => decide (x.val = 97 + k)).length

def minRange (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range (n + 1)).foldr (fun k acc => min (f k) acc) (f 0)

def maxRange (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range (n + 1)).foldr (fun k acc => max (f k) acc) (f 0)

def c1Cost (a b : List U8) : ℕ :=
  minRange 24 (fun k => countGt a (k : ℤ) + countLe b (k : ℤ))

def c2Cost (a b : List U8) : ℕ :=
  minRange 24 (fun k => countLe a (k : ℤ) + countGt b (k : ℤ))

def c3Cost (a b : List U8) : ℕ :=
  (a.length - maxRange 25 (fun k => countOfOffset a k)) +
    (b.length - maxRange 25 (fun k => countOfOffset b k))

def closedFormMin (a b : List U8) : ℕ := min (c1Cost a b) (min (c2Cost a b) (c3Cost a b))

/-- Whenever min_characters a b returns a result r, the following holds. A target pair is a pair of byte slices (A', B') with len(A') = len(a), len(B') = len(b), and every byte in 'a'..'z'. Its change cost is cost(A',B') = (number of i with 0 <= i < len(a) and A'[i] != a[i]) + (number of j with 0 <= j < len(b) and B'[j] != b[j]). The target pair is admissible if either (1) A'[i] < B'[j] for every i,j, or (2) B'[j] < A'[i] for every i,j, or (3) all bytes of A' are equal and all bytes of B' are equal. Then r equals the minimum of cost(A',B') over all admissible target pairs.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_1 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    (∀ A' B', IsTargetPair A' B' a b → AdmissiblePair A' B' →
        r.val ≤ (changeCost A' B' a.val b.val : ℤ)) ∧
      ∃ A' B', IsTargetPair A' B' a b ∧ AdmissiblePair A' B' ∧
        (changeCost A' B' a.val b.val : ℤ) = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), (∀ A' B', IsTargetPair A' B' a b → AdmissiblePair A' B' →
        r.val ≤ (changeCost A' B' a.val b.val : ℤ)) ∧
      ∃ A' B', IsTargetPair A' B' a b ∧ AdmissiblePair A' B' ∧
        (changeCost A' B' a.val b.val : ℤ) = r.val) := by
  sorry

/-- The call min_characters a b does not fail: it returns Result.ok r for some i64 r.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_2 (a b : Slice U8)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val) :
    ∃ r : I64, Aegis.MinCharacters.min_characters a b = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b : Slice U8)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val), ∃ r : I64, Aegis.MinCharacters.min_characters a b = ok r) := by
  sorry

/-- Whenever min_characters a b returns a result r, 0 <= r.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_3 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever min_characters a b returns a result r, r <= len(a) + len(b).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_4 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    r.val ≤ ((a.val.length + b.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), r.val ≤ ((a.val.length + b.val.length : ℕ) : ℤ)) := by
  sorry

/-- For every integer k with 0 <= k <= 24, whenever min_characters a b returns a result r, r <= (number of i with 0 <= i < len(a) and (a[i] - 97) > k) + (number of j with 0 <= j < len(b) and (b[j] - 97) <= k).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_5 (a b : Slice U8) (r : I64) (k : ℤ) (_hk0 : 0 ≤ k) (_hk24 : k ≤ 24)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    r.val ≤ ((countGt a.val k + countLe b.val k : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : Slice U8) (r : I64) (k : ℤ) (_hk0 : 0 ≤ k) (_hk24 : k ≤ 24)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), r.val ≤ ((countGt a.val k + countLe b.val k : ℕ) : ℤ)) := by
  sorry

/-- For every integer k with 0 <= k <= 24, whenever min_characters a b returns a result r, r <= (number of i with 0 <= i < len(a) and (a[i] - 97) <= k) + (number of j with 0 <= j < len(b) and (b[j] - 97) > k).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_6 (a b : Slice U8) (r : I64) (k : ℤ) (_hk0 : 0 ≤ k) (_hk24 : k ≤ 24)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    r.val ≤ ((countLe a.val k + countGt b.val k : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b : Slice U8) (r : I64) (k : ℤ) (_hk0 : 0 ≤ k) (_hk24 : k ≤ 24)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), r.val ≤ ((countLe a.val k + countGt b.val k : ℕ) : ℤ)) := by
  sorry

/-- For every lowercase byte x and every lowercase byte y, whenever min_characters a b returns a result r, r <= (len(a) - (number of i with 0 <= i < len(a) and a[i] = x)) + (len(b) - (number of j with 0 <= j < len(b) and b[j] = y)).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_7 (a b : Slice U8) (r : I64) (x y : U8)
    (_hx : IsLowerByte x) (_hy : IsLowerByte y)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    r.val ≤ (((a.val.length - countOfByte a.val x) +
      (b.val.length - countOfByte b.val y) : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b : Slice U8) (r : I64) (x y : U8)
    (_hx : IsLowerByte x) (_hy : IsLowerByte y)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), r.val ≤ (((a.val.length - countOfByte a.val x) +
      (b.val.length - countOfByte b.val y) : ℕ) : ℤ)) := by
  sorry

/-- Whenever min_characters a b returns a result r, r = 0 if and only if at least one of the following holds: (i) a[i] < b[j] for every i with 0 <= i < len(a) and every j with 0 <= j < len(b); (ii) b[j] < a[i] for every i with 0 <= i < len(a) and every j with 0 <= j < len(b); (iii) all bytes of a are equal and all bytes of b are equal.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_8 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    r.val = 0 ↔ AdmissiblePair a.val b.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), r.val = 0 ↔ AdmissiblePair a.val b.val) := by
  sorry

/-- Whenever min_characters a b returns a result r, there exists a target pair (A', B') with len(A') = len(a), len(B') = len(b), and all bytes in 'a'..'z' such that either (1) A'[i] < B'[j] for every i,j, or (2) B'[j] < A'[i] for every i,j, or (3) all bytes of A' are equal and all bytes of B' are equal; and the number of changed positions (number of i with A'[i] != a[i] plus number of j with B'[j] != b[j]) is exactly r.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_9 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    ∃ A' B', IsTargetPair A' B' a b ∧ AdmissiblePair A' B' ∧
      (changeCost A' B' a.val b.val : ℤ) = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), ∃ A' B', IsTargetPair A' B' a b ∧ AdmissiblePair A' B' ∧
      (changeCost A' B' a.val b.val : ℤ) = r.val) := by
  sorry

/-- Whenever min_characters a b returns a result r, for every target pair (A', B') with len(A') = len(a), len(B') = len(b), and all bytes in 'a'..'z' that satisfies either (1) A'[i] < B'[j] for every i,j, or (2) B'[j] < A'[i] for every i,j, or (3) all bytes of A' are equal and all bytes of B' are equal, the change count (number of i with A'[i] != a[i] plus number of j with B'[j] != b[j]) is at least r.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_10 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    ∀ A' B', IsTargetPair A' B' a b → AdmissiblePair A' B' →
      r.val ≤ (changeCost A' B' a.val b.val : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), ∀ A' B', IsTargetPair A' B' a b → AdmissiblePair A' B' →
      r.val ≤ (changeCost A' B' a.val b.val : ℤ)) := by
  sorry

/-- For any a and b satisfying the preconditions, if min_characters a b returns r and min_characters b a returns r', then r = r'.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_11 (a b : Slice U8) (r r' : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r)
    (hr' : Aegis.MinCharacters.min_characters b a = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b : Slice U8) (r r' : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r)
    (hr' : Aegis.MinCharacters.min_characters b a = ok r'), r.val = r'.val) := by
  sorry

/-- Let a' and b' be any byte slices such that len(a') = len(a), len(b') = len(b), and for every lowercase byte c the number of occurrences of c in a' equals that in a and the number of occurrences of c in b' equals that in b (so a' and b' are arbitrary reorderings of a and b). If min_characters a b returns r and min_characters a' b' returns r', then r = r'.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_12 (a b a' b' : Slice U8) (r r' : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (_hlena : a'.val.length = a.val.length)
    (_hlenb : b'.val.length = b.val.length)
    (_hca : ∀ c : U8, IsLowerByte c → countOfByte a'.val c = countOfByte a.val c)
    (_hcb : ∀ c : U8, IsLowerByte c → countOfByte b'.val c = countOfByte b.val c)
    (hr : Aegis.MinCharacters.min_characters a b = ok r)
    (hr' : Aegis.MinCharacters.min_characters a' b' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b a' b' : Slice U8) (r r' : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (_hlena : a'.val.length = a.val.length)
    (_hlenb : b'.val.length = b.val.length)
    (_hca : ∀ c : U8, IsLowerByte c → countOfByte a'.val c = countOfByte a.val c)
    (_hcb : ∀ c : U8, IsLowerByte c → countOfByte b'.val c = countOfByte b.val c)
    (hr : Aegis.MinCharacters.min_characters a b = ok r)
    (hr' : Aegis.MinCharacters.min_characters a' b' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever min_characters a b returns a result r, r equals the minimum of these three quantities: (C1) min over k = 0..24 of (number of i with 0 <= i < len(a) and a[i]-97 > k) + (number of j with 0 <= j < len(b) and b[j]-97 <= k); (C2) min over k = 0..24 of (number of i with 0 <= i < len(a) and a[i]-97 <= k) + (number of j with 0 <= j < len(b) and b[j]-97 > k); (C3) (len(a) - max over c in 'a'..'z' of number of i with 0 <= i < len(a) and a[i] = c) + (len(b) - max over c in 'a'..'z' of number of j with 0 <= j < len(b) and b[j] = c).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100000, len(b) <= 100000, and every byte of a and b is in the ASCII range 97 ('a') through 122 ('z'). -/
theorem spec_13 (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r) :
    r.val = (closedFormMin a.val b.val : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (a b : Slice U8) (r : I64)
    (_ha1 : 1 ≤ a.val.length) (_hb1 : 1 ≤ b.val.length)
    (_ha2 : a.val.length ≤ 100000) (_hb2 : b.val.length ≤ 100000)
    (_haL : AllLowerBytes a.val) (_hbL : AllLowerBytes b.val)
    (hr : Aegis.MinCharacters.min_characters a b = ok r), r.val = (closedFormMin a.val b.val : ℤ)) := by
  sorry

end AegisSpec.MinCharacters
