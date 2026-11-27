import Aegis.StringSequence.Code.Funs

/-!
# Specifications of `Aegis.StringSequence.string_sequence`

LeetCode problem `find-the-sequence-of-strings-appeared-on-the-screen`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.StringSequence

namespace AegisSpec.StringSequence

def partialSum (target : Slice Std.U8) (k : ℕ) : ℕ :=
  ((target.val.take k).map (fun b => b.val - 96)).sum

def byteAt? (l : List Std.U8) (j : ℕ) : Option ℕ :=
  (l[j]?).map (fun b => b.val)

def StepAppend (prev cur : alloc.vec.Vec Std.U8) : Prop :=
  cur.val.length = prev.val.length + 1 ∧
    (∀ (j : ℕ), (hj : j < prev.val.length) → cur.val[j]? = prev.val[j]?) ∧
    cur.val[prev.val.length]? = some (97#u8)

def StepIncrement (prev cur : alloc.vec.Vec Std.U8) : Prop :=
  cur.val.length = prev.val.length ∧
    (∀ (j : ℕ), (hj : j < cur.val.length - 1) → cur.val[j]? = prev.val[j]?) ∧
    ∃ (b b' : Std.U8),
      cur.val[cur.val.length - 1]? = some b ∧
        prev.val[prev.val.length - 1]? = some b' ∧ b.val = b'.val + 1

/-- Let n = len(target). For each i with 0 <= i < n, let c_i = target[i] - 97. Define S_0 = 0 and for k = 0, ..., n-1, S_{k+1} = S_k + (c_k + 1). Whenever string_sequence(target) returns a result r, the following holds: len(r) = S_n; and for every k with 0 <= k < n and every t with 0 <= t <= c_k, the element r[S_k + t] is the byte string of length k+1 such that for all j with 0 <= j < k, r[S_k + t][j] = target[j], and r[S_k + t][k] = 97 + t.
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122 (so target[i] is the ASCII code of a lowercase English letter). -/
theorem spec_1 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      r.val.length = partialSum target target.val.length ∧
        ∀ (k : ℕ), (hk : k < target.val.length) →
          ∀ (t : ℕ), (ht : t ≤ (target.val[k]).val - 97) →
            ∃ (v : alloc.vec.Vec Std.U8) (b : Std.U8),
              r.val[partialSum target k + t]? = some v ∧
                v.val.length = k + 1 ∧
                (∀ (j : ℕ), (hj : j < k) → v.val[j]? = target.val[j]?) ∧
                v.val[k]? = some b ∧ b.val = 97 + t := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      r.val.length = partialSum target target.val.length ∧
        ∀ (k : ℕ), (hk : k < target.val.length) →
          ∀ (t : ℕ), (ht : t ≤ (target.val[k]).val - 97) →
            ∃ (v : alloc.vec.Vec Std.U8) (b : Std.U8),
              r.val[partialSum target k + t]? = some v ∧
                v.val.length = k + 1 ∧
                (∀ (j : ℕ), (hj : j < k) → v.val[j]? = target.val[j]?) ∧
                v.val[k]? = some b ∧ b.val = 97 + t) := by
  sorry

/-- For every target satisfying the preconditions, string_sequence(target) returns a result r (it does not fail, panic, or overflow).
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_2 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), string_sequence target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), string_sequence target = ok r) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, len(r) = Σ_{i=0}^{n-1} (target[i] - 96), where n = len(target). Equivalently, len(r) = n + Σ_{i=0}^{n-1} (target[i] - 97).
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_3 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      r.val.length = partialSum target target.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      r.val.length = partialSum target target.val.length) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, for every index p with 0 <= p < len(r), let L = len(r[p]). Then: (1) 1 <= L <= n; (2) for every j with 0 <= j < L-1, r[p][j] = target[j]; (3) 97 <= r[p][L-1] <= target[L-1].
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_4 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp : p < r.val.length) →
        ∀ (v : alloc.vec.Vec Std.U8), r.val[p]? = some v →
          1 ≤ v.val.length ∧
            v.val.length ≤ target.val.length ∧
            (∀ (j : ℕ), (hj : j < v.val.length - 1) → v.val[j]? = target.val[j]?) ∧
            (∀ (a b : ℕ), byteAt? v.val (v.val.length - 1) = some a →
              byteAt? target.val (v.val.length - 1) = some b → 97 ≤ a ∧ a ≤ b) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp : p < r.val.length) →
        ∀ (v : alloc.vec.Vec Std.U8), r.val[p]? = some v →
          1 ≤ v.val.length ∧
            v.val.length ≤ target.val.length ∧
            (∀ (j : ℕ), (hj : j < v.val.length - 1) → v.val[j]? = target.val[j]?) ∧
            (∀ (a b : ℕ), byteAt? v.val (v.val.length - 1) = some a →
              byteAt? target.val (v.val.length - 1) = some b → 97 ≤ a ∧ a ≤ b)) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, for every p with 1 <= p < len(r), exactly one of the following holds: (a) len(r[p]) = len(r[p-1]) + 1, r[p][j] = r[p-1][j] for all j with 0 <= j < len(r[p-1]), and r[p][len(r[p-1])] = 97; or (b) len(r[p]) = len(r[p-1]), r[p][j] = r[p-1][j] for all j with 0 <= j < len(r[p]) - 1, and r[p][len(r[p]) - 1] = r[p-1][len(r[p-1]) - 1] + 1.
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_5 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp1 : 1 ≤ p) → (hp2 : p < r.val.length) →
        ∀ (prev cur : alloc.vec.Vec Std.U8), r.val[p - 1]? = some prev →
          r.val[p]? = some cur → Xor (StepAppend prev cur) (StepIncrement prev cur) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp1 : 1 ≤ p) → (hp2 : p < r.val.length) →
        ∀ (prev cur : alloc.vec.Vec Std.U8), r.val[p - 1]? = some prev →
          r.val[p]? = some cur → Xor (StepAppend prev cur) (StepIncrement prev cur)) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, the elements of r are pairwise distinct: for every i, j with 0 <= i < j < len(r), r[i] ≠ r[j].
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_6 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (i j : ℕ), (hi : i < j) → (hj : j < r.val.length) →
        r.val[i]? ≠ r.val[j]? := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (i j : ℕ), (hi : i < j) → (hj : j < r.val.length) →
        r.val[i]? ≠ r.val[j]?) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, for each k with 0 <= k < n, the number of indices p in [0, len(r)-1] such that len(r[p]) = k+1 is exactly (target[k] - 97) + 1.
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_7 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (k : ℕ), (hk : k < target.val.length) →
        (r.val.filter (fun v => v.val.length == k + 1)).length =
          (target.val[k]).val - 97 + 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (k : ℕ), (hk : k < target.val.length) →
        (r.val.filter (fun v => v.val.length == k + 1)).length =
          (target.val[k]).val - 97 + 1) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, every byte in every string of r is a lowercase English letter: for every p with 0 <= p < len(r) and every j with 0 <= j < len(r[p]), 97 <= r[p][j] <= 122.
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_8 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp : p < r.val.length) →
        ∀ (v : alloc.vec.Vec Std.U8), r.val[p]? = some v →
          ∀ (j : ℕ), (hj : j < v.val.length) →
            97 ≤ (v.val[j]).val ∧ (v.val[j]).val ≤ 122 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp : p < r.val.length) →
        ∀ (v : alloc.vec.Vec Std.U8), r.val[p]? = some v →
          ∀ (j : ℕ), (hj : j < v.val.length) →
            97 ≤ (v.val[j]).val ∧ (v.val[j]).val ≤ 122) := by
  sorry

/-- Whenever string_sequence(target) returns a result r, the lengths of the strings in r are nondecreasing: for every p with 0 <= p < len(r)-1, len(r[p]) <= len(r[p+1]).
  Preconditions: target is a byte slice with 1 <= len(target) <= 400, and for every i with 0 <= i < len(target), 97 <= target[i] <= 122. -/
theorem spec_9 (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp : p < r.val.length - 1) →
        ∀ (v w : alloc.vec.Vec Std.U8), r.val[p]? = some v → r.val[p + 1]? = some w →
          v.val.length ≤ w.val.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target : Slice Std.U8)
    (h1 : 1 ≤ target.val.length) (h2 : target.val.length ≤ 400)
    (h3 : ∀ (i : ℕ), (hi : i < target.val.length) →
      97 ≤ (target.val[i]).val ∧ (target.val[i]).val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)), string_sequence target = ok r →
      ∀ (p : ℕ), (hp : p < r.val.length - 1) →
        ∀ (v w : alloc.vec.Vec Std.U8), r.val[p]? = some v → r.val[p + 1]? = some w →
          v.val.length ≤ w.val.length) := by
  sorry

end AegisSpec.StringSequence
