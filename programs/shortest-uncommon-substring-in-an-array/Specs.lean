import Aegis.ShortestSubstrings.Code.Funs

/-!
# Specifications of `Aegis.ShortestSubstrings.shortest_substrings`

LeetCode problem `shortest-uncommon-substring-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ShortestSubstrings

def OccursAt (u s : List Std.U8) (p : Nat) : Prop :=
  p + u.length ≤ s.length ∧ ∀ t : Nat, t < u.length → s[p + t]? = u[t]?

def IsSubstring (u s : List Std.U8) : Prop :=
  u ≠ [] ∧ ∃ p : Nat, OccursAt u s p

def OccurringBytes (c : Std.U8) (s : List Std.U8) : Prop :=
  ∃ k : Nat, k < s.length ∧ s[k]? = some c

def otherArrays (arr : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List (List Std.U8) :=
  (arr.val.eraseIdx i).map (fun s => s.val)

def AbsentElsewhere (others : List (List Std.U8)) (u : List Std.U8) : Prop :=
  ∀ v ∈ others, ¬ IsSubstring u v

def UniqueSubstring (s : List Std.U8) (others : List (List Std.U8)) (u : List Std.U8) : Prop :=
  IsSubstring u s ∧ AbsentElsewhere others u

def ByteUniqueTo (s : List Std.U8) (others : List (List Std.U8)) (c : Std.U8) : Prop :=
  OccurringBytes c s ∧ ∀ v ∈ others, ¬ OccurringBytes c v

def LexLe : List Std.U8 → List Std.U8 → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: a', b :: b' => a.val < b.val ∨ (a.val = b.val ∧ LexLe a' b')

/-- The function returns a result r and does not fail. It holds that len(r) = n. Define: u is a substring of s iff u is non-empty and there exists p with 0 <= p <= len(s)-len(u) such that for all t with 0 <= t < len(u), u[t] = s[p+t]. Define u <=lex v to be the usual lexicographic order on byte arrays: u is a prefix of v (including u = v), or at the first index k where u and v differ, u[k] < v[k], comparing bytes as natural numbers. Then for every i with 0 <= i < n: if there exists a byte array u that is a substring of arr[i] and is not a substring of arr[j] for every j with 0 <= j < n and j != i, then r[i] is a substring of arr[i], r[i] is not a substring of any arr[j] with j != i, len(r[i]) <= len(u) for every such u, and r[i] <=lex u for every such u with len(u) = len(r[i]). If no such u exists, then r[i] is the empty byte array.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). Indices are 0-based. -/
theorem spec_1 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r ∧
      r.val.length = arr.val.length ∧
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        ((∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          (IsSubstring (r.val[i]).val (arr.val[i]).val ∧
           AbsentElsewhere (otherArrays arr i) (r.val[i]).val ∧
           (∀ u : List Std.U8,
              UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
              (r.val[i]).val.length ≤ u.length) ∧
           ∀ u : List Std.U8,
              UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
              u.length = (r.val[i]).val.length → LexLe (r.val[i]).val u)) ∧
        ((¬ ∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          (r.val[i]).val = []) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r ∧
      r.val.length = arr.val.length ∧
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        ((∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          (IsSubstring (r.val[i]).val (arr.val[i]).val ∧
           AbsentElsewhere (otherArrays arr i) (r.val[i]).val ∧
           (∀ u : List Std.U8,
              UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
              (r.val[i]).val.length ≤ u.length) ∧
           ∀ u : List Std.U8,
              UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
              u.length = (r.val[i]).val.length → LexLe (r.val[i]).val u)) ∧
        ((¬ ∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          (r.val[i]).val = [])) := by
  sorry

/-- For every arr satisfying the preconditions, the function returns a result r; it does not panic, overflow, go out of bounds, or otherwise fail.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_2 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(arr).
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_3 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r → r.val.length = arr.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r → r.val.length = arr.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if r[i] is non-empty then: (a) there exists p with 0 <= p <= len(arr[i]) - len(r[i]) such that for all t with 0 <= t < len(r[i]), r[i][t] = arr[i][p+t]; and (b) for every j with 0 <= j < len(arr) and j != i, there is no q with 0 <= q <= len(arr[j]) - len(r[i]) such that for all t with 0 <= t < len(r[i]), r[i][t] = arr[j][q+t].
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_4 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (r.val[i]).val ≠ [] →
          (∃ p : Nat, OccursAt (r.val[i]).val (arr.val[i]).val p) ∧
          (∀ (j : Nat) (hj : j < arr.val.length), j ≠ i →
            ¬ ∃ q : Nat, OccursAt (r.val[i]).val (arr.val[j]).val q) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (r.val[i]).val ≠ [] →
          (∃ p : Nat, OccursAt (r.val[i]).val (arr.val[i]).val p) ∧
          (∀ (j : Nat) (hj : j < arr.val.length), j ≠ i →
            ¬ ∃ q : Nat, OccursAt (r.val[i]).val (arr.val[j]).val q)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), r[i] is the empty byte array if and only if there is no non-empty byte array u for which there exists p with 0 <= p <= len(arr[i]) - len(u) and (for all t with 0 <= t < len(u), u[t] = arr[i][p+t]) and, for every j with 0 <= j < len(arr) and j != i, there is no q with 0 <= q <= len(arr[j]) - len(u) and (for all t with 0 <= t < len(u), u[t] = arr[j][q+t]).
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_5 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        ((r.val[i]).val = [] ↔
          ¬ ∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        ((r.val[i]).val = [] ↔
          ¬ ∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if there exists at least one non-empty byte array u that is a substring of arr[i] and is not a substring of any arr[j] with j != i (substring means contiguous non-empty occurrence), then r[i] is non-empty and len(r[i]) <= len(u) for every such u.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_6 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          (r.val[i]).val ≠ [] ∧
          ∀ u : List Std.U8,
            UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
            (r.val[i]).val.length ≤ u.length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          (r.val[i]).val ≠ [] ∧
          ∀ u : List Std.U8,
            UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
            (r.val[i]).val.length ≤ u.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if there exists at least one non-empty byte array u that is a substring of arr[i] and is not a substring of any arr[j] with j != i (substring means contiguous non-empty occurrence), then for every such u with len(u) = len(r[i]), r[i] <=lex u, where <=lex is the usual lexicographic order on byte arrays.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_7 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          ∀ u : List Std.U8,
            UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
            u.length = (r.val[i]).val.length → LexLe (r.val[i]).val u := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ u : List Std.U8, UniqueSubstring (arr.val[i]).val (otherArrays arr i) u) →
          ∀ u : List Std.U8,
            UniqueSubstring (arr.val[i]).val (otherArrays arr i) u →
            u.length = (r.val[i]).val.length → LexLe (r.val[i]).val u) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), every non-empty byte array u that is a substring of r[i] and has len(u) < len(r[i]) is a substring of arr[j] for at least one j with 0 <= j < len(arr) and j != i. (Substring means contiguous occurrence.)
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_8 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        ∀ (u : List Std.U8),
          IsSubstring u (r.val[i]).val → u.length < (r.val[i]).val.length →
            ∃ (j : Nat) (hj : j < arr.val.length), j ≠ i ∧ IsSubstring u (arr.val[j]).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        ∀ (u : List Std.U8),
          IsSubstring u (r.val[i]).val → u.length < (r.val[i]).val.length →
            ∃ (j : Nat) (hj : j < arr.val.length), j ≠ i ∧ IsSubstring u (arr.val[j]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if there exists j with 0 <= j < len(arr), j != i, and arr[j] = arr[i] (byte-for-byte equality), then r[i] is the empty byte array.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_9 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ (j : Nat) (hj : j < arr.val.length), j ≠ i ∧ (arr.val[j]).val = (arr.val[i]).val) →
          (r.val[i]).val = [] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ (j : Nat) (hj : j < arr.val.length), j ≠ i ∧ (arr.val[j]).val = (arr.val[i]).val) →
          (r.val[i]).val = []) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), let C be the set of bytes c with 97 <= c <= 122 such that there exists k with 0 <= k < len(arr[i]) and arr[i][k] = c, and for every j with 0 <= j < len(arr) and j != i there is no k with 0 <= k < len(arr[j]) and arr[j][k] = c. If C is non-empty, then len(r[i]) = 1 and r[i][0] is the least byte in C (equivalently the lexicographically smallest one-byte string from C).
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_10 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ c : Std.U8,
          97 ≤ c.val ∧ c.val ≤ 122 ∧
            ByteUniqueTo (arr.val[i]).val (otherArrays arr i) c) →
          ∃ b : Std.U8,
            (r.val[i]).val = [b] ∧
            97 ≤ b.val ∧ b.val ≤ 122 ∧
            ByteUniqueTo (arr.val[i]).val (otherArrays arr i) b ∧
            (∀ c : Std.U8,
              97 ≤ c.val ∧ c.val ≤ 122 →
                ByteUniqueTo (arr.val[i]).val (otherArrays arr i) c → b.val ≤ c.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (∃ c : Std.U8,
          97 ≤ c.val ∧ c.val ≤ 122 ∧
            ByteUniqueTo (arr.val[i]).val (otherArrays arr i) c) →
          ∃ b : Std.U8,
            (r.val[i]).val = [b] ∧
            97 ≤ b.val ∧ b.val ≤ 122 ∧
            ByteUniqueTo (arr.val[i]).val (otherArrays arr i) b ∧
            (∀ c : Std.U8,
              97 ≤ c.val ∧ c.val ≤ 122 →
                ByteUniqueTo (arr.val[i]).val (otherArrays arr i) c → b.val ≤ c.val)) := by
  sorry

/-- Whenever the function returns a result r, for every i and k with 0 <= i < len(arr) and 0 <= k < len(r[i]), the byte r[i][k] satisfies 97 <= r[i][k] <= 122.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_11 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length)
        (k : Nat) (hk : k < (r.val[i]).val.length),
          97 ≤ ((r.val[i]).val[k]).val ∧ ((r.val[i]).val[k]).val ≤ 122 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length)
        (k : Nat) (hk : k < (r.val[i]).val.length),
          97 ≤ ((r.val[i]).val[k]).val ∧ ((r.val[i]).val[k]).val ≤ 122) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), len(r[i]) <= len(arr[i]); consequently, by the constraints, len(r[i]) <= 20.
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_12 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (r.val[i]).val.length ≤ (arr.val[i]).val.length ∧ (r.val[i]).val.length ≤ 20 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (r.val[i]).val.length ≤ (arr.val[i]).val.length ∧ (r.val[i]).val.length ≤ 20) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr) and len(arr[i]) = 1, r[i] = arr[i] if arr[i] is not a substring of any arr[j] with j != i, and r[i] is the empty byte array otherwise. (Substring means contiguous occurrence.)
  Preconditions: Let n = len(arr). The input arr satisfies the problem constraints: 2 <= n <= 100; for every i with 0 <= i < n, 1 <= len(arr[i]) <= 20 and every byte of arr[i] is in {97,...,122} (lowercase English letters). -/
theorem spec_13 (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (arr.val[i]).val.length = 1 →
          ((AbsentElsewhere (otherArrays arr i) (arr.val[i]).val →
              (r.val[i]).val = (arr.val[i]).val) ∧
            (¬ AbsentElsewhere (otherArrays arr i) (arr.val[i]).val →
              (r.val[i]).val = [])) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice (alloc.vec.Vec Std.U8))
    (hn_ge : 2 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100)
    (harr_pos : ∀ (i : Nat) (hi : i < arr.val.length), 1 ≤ (arr.val[i]).val.length)
    (harr_cap : ∀ (i : Nat) (hi : i < arr.val.length), (arr.val[i]).val.length ≤ 20)
    (hbytes : ∀ (i : Nat) (hi : i < arr.val.length) (b : Std.U8),
      b ∈ (arr.val[i]).val → 97 ≤ b.val ∧ b.val ≤ 122), ∀ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)),
      Aegis.ShortestSubstrings.shortest_substrings arr = ok r →
      ∀ (hlen : r.val.length = arr.val.length) (i : Nat) (hi : i < arr.val.length),
        (arr.val[i]).val.length = 1 →
          ((AbsentElsewhere (otherArrays arr i) (arr.val[i]).val →
              (r.val[i]).val = (arr.val[i]).val) ∧
            (¬ AbsentElsewhere (otherArrays arr i) (arr.val[i]).val →
              (r.val[i]).val = []))) := by
  sorry

end AegisSpec.ShortestSubstrings
