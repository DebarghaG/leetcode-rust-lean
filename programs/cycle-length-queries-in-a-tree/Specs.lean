import Aegis.CycleLengthQueries.Code.Funs

/-!
# Specifications of `Aegis.CycleLengthQueries.cycle_length_queries`

LeetCode problem `cycle-length-queries-in-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CycleLengthQueries

def depth (x : ℤ) : ℤ := (Nat.log2 x.toNat : ℤ)

def IsAncestor (u v : ℤ) : Prop := ∃ k : ℕ, u = v / (2 : ℤ) ^ k

def lca (a b : ℤ) : ℤ :=
  let da := depth a
  let db := depth b
  let d := min da db
  let A := a / (2 : ℤ) ^ (da - d).toNat
  let B := b / (2 : ℤ) ^ (db - d).toNat
  match (List.range (d.toNat + 1)).find? (fun j => decide (A / (2 : ℤ) ^ j = B / (2 : ℤ) ^ j)) with
  | some j => A / (2 : ℤ) ^ j
  | none => 1

def treeDist (a b : ℤ) : ℤ := depth a + depth b - 2 * depth (lca a b)

def nodeBound (n : Std.I64) : ℤ := 2 ^ n.val.toNat - 1

def queryAt? (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ) :=
  match queries.val[i]? with
  | none => none
  | some q =>
    match q.slice.val with
    | [a, b] => some (a.val, b.val)
    | _ => none

def answerAt? (r : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ :=
  (r.slice.val[i]?).map (fun x => x.val)

/-- Whenever the function returns a result r, len(r) = m and for every i with 0 <= i < m, r[i] = treeDist(a_i, b_i) + 1. Here depth(x), for x >= 1, is the unique d >= 0 with 2^d <= x < 2^(d+1); u is an ancestor of v if u = floor(v / 2^k) for some k >= 0; lca(a,b) is the common ancestor of a and b of maximum depth; and treeDist(a,b) = depth(a) + depth(b) - 2*depth(lca(a,b)), which is the number of edges on the unique simple path between a and b in the complete binary tree with nodes {1,...,2^n - 1} and parent of x > 1 equal to floor(x/2).
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_1
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    r.slice.val.length = queries.val.length ∧
      ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
        answerAt? r i = some (treeDist a b + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), r.slice.val.length = queries.val.length ∧
      ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
        answerAt? r i = some (treeDist a b + 1)) := by
  sorry

/-- Under these preconditions the function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_2
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, 2 <= r[i] <= 2*n - 1.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_3
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ i : ℕ, i < queries.val.length →
      ∃ z : ℤ, answerAt? r i = some z ∧ 2 ≤ z ∧ z ≤ 2 * n.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ i : ℕ, i < queries.val.length →
      ∃ z : ℤ, answerAt? r i = some z ∧ 2 ≤ z ∧ z ≤ 2 * n.val - 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m: if a_i is an ancestor of b_i (that is, a_i = floor(b_i / 2^k) for some k >= 0), then r[i] = depth(b_i) - depth(a_i) + 1; symmetrically, if b_i is an ancestor of a_i, then r[i] = depth(a_i) - depth(b_i) + 1. Here depth(x) is the unique d >= 0 with 2^d <= x < 2^(d+1).
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_4
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      (IsAncestor a b → answerAt? r i = some (depth b - depth a + 1)) ∧
        (IsAncestor b a → answerAt? r i = some (depth a - depth b + 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      (IsAncestor a b → answerAt? r i = some (depth b - depth a + 1)) ∧
        (IsAncestor b a → answerAt? r i = some (depth a - depth b + 1))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if floor(a_i/2) = floor(b_i/2), then r[i] = 3.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_5
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      a / 2 = b / 2 → answerAt? r i = some 3 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      a / 2 = b / 2 → answerAt? r i = some 3) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0 <= i < m and 0 <= j < m, if a_i = b_j and b_i = a_j, then r[i] = r[j]. Thus the answer for a query does not depend on the order of its two endpoints.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_6
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i j : ℕ) (a b a' b' : ℤ), i < queries.val.length → j < queries.val.length →
      queryAt? queries i = some (a, b) → queryAt? queries j = some (a', b') →
        a = b' → b = a' → answerAt? r i = answerAt? r j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i j : ℕ) (a b a' b' : ℤ), i < queries.val.length → j < queries.val.length →
      queryAt? queries i = some (a, b) → queryAt? queries j = some (a', b') →
        a = b' → b = a' → answerAt? r i = answerAt? r j) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, r[i] mod 2 = (depth(a_i) + depth(b_i) + 1) mod 2, where depth(x) is the unique d >= 0 with 2^d <= x < 2^(d+1).
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_7
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      ∃ z : ℤ, answerAt? r i = some z ∧ z % 2 = (depth a + depth b + 1) % 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      ∃ z : ℤ, answerAt? r i = some z ∧ z % 2 = (depth a + depth b + 1) % 2) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if neither a_i is an ancestor of b_i nor b_i is an ancestor of a_i (where u is an ancestor of v iff u = floor(v / 2^k) for some k >= 0), then r[i] >= 3.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_8
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      ¬ IsAncestor a b → ¬ IsAncestor b a → ∃ z : ℤ, answerAt? r i = some z ∧ 3 ≤ z := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      ¬ IsAncestor a b → ¬ IsAncestor b a → ∃ z : ℤ, answerAt? r i = some z ∧ 3 ≤ z) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if neither endpoint is an ancestor of the other (u is an ancestor of v iff u = floor(v / 2^k) for some k >= 0) and floor(a_i/2) != floor(b_i/2), then r[i] >= 4.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_9
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      ¬ IsAncestor a b → ¬ IsAncestor b a → a / 2 ≠ b / 2 →
        ∃ z : ℤ, answerAt? r i = some z ∧ 4 ≤ z := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      ¬ IsAncestor a b → ¬ IsAncestor b a → a / 2 ≠ b / 2 →
        ∃ z : ℤ, answerAt? r i = some z ∧ 4 ≤ z) := by
  sorry

/-- For every integer n' with n <= n' <= 30, let r be a result returned by cycle_length_queries(n, queries) and let r' be a result returned by cycle_length_queries(n', queries). Whenever both calls return results, len(r') = len(r) = m and for every i with 0 <= i < m, r'[i] = r[i].
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_10
    (n n' : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30) (hn'_lo : n.val ≤ n'.val) (hn'_hi : n'.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r)
    (r' : alloc.vec.Vec Std.I64)
    (hr' : Aegis.CycleLengthQueries.cycle_length_queries n' queries = ok r') :
    r'.slice.val.length = queries.val.length ∧ r.slice.val.length = queries.val.length ∧
      ∀ i : ℕ, i < queries.val.length → answerAt? r' i = answerAt? r i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n n' : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30) (hn'_lo : n.val ≤ n'.val) (hn'_hi : n'.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r)
    (r' : alloc.vec.Vec Std.I64)
    (hr' : Aegis.CycleLengthQueries.cycle_length_queries n' queries = ok r'), r'.slice.val.length = queries.val.length ∧ r.slice.val.length = queries.val.length ∧
      ∀ i : ℕ, i < queries.val.length → answerAt? r' i = answerAt? r i) := by
  sorry

/-- Let queries' be any other slice of vectors satisfying the same preconditions with the same n and the same length m. Whenever cycle_length_queries(n, queries) returns r and cycle_length_queries(n, queries') returns r', for every i with 0 <= i < m such that queries'[i][0] = a_i and queries'[i][1] = b_i, we have r[i] = r'[i]. Thus the i-th answer depends only on the i-th query, not on the other queries.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_11
    (n : Std.I64) (queries queries' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (hm'_lo : 1 ≤ queries'.val.length) (hm'_hi : queries'.val.length ≤ 100000)
    (hq' : ∀ i : ℕ, i < queries'.val.length → ∃ a b : ℤ,
      queryAt? queries' i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (hlen : queries'.val.length = queries.val.length)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r)
    (r' : alloc.vec.Vec Std.I64)
    (hr' : Aegis.CycleLengthQueries.cycle_length_queries n queries' = ok r') :
    ∀ (i : ℕ) (a b a' b' : ℤ), i < queries.val.length →
      queryAt? queries i = some (a, b) → queryAt? queries' i = some (a', b') →
        a' = a → b' = b → answerAt? r i = answerAt? r' i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (queries queries' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (hm'_lo : 1 ≤ queries'.val.length) (hm'_hi : queries'.val.length ≤ 100000)
    (hq' : ∀ i : ℕ, i < queries'.val.length → ∃ a b : ℤ,
      queryAt? queries' i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (hlen : queries'.val.length = queries.val.length)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r)
    (r' : alloc.vec.Vec Std.I64)
    (hr' : Aegis.CycleLengthQueries.cycle_length_queries n queries' = ok r'), ∀ (i : ℕ) (a b a' b' : ℤ), i < queries.val.length →
      queryAt? queries i = some (a, b) → queryAt? queries' i = some (a', b') →
        a' = a → b' = b → answerAt? r i = answerAt? r' i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if depth(a_i) = depth(b_i) = n - 1 and lca(a_i,b_i) = 1 (the root), then r[i] = 2*n - 1. Here depth(x) is the unique d >= 0 with 2^d <= x < 2^(d+1), and lca(a,b) is the deepest common ancestor of a and b.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_12
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      depth a = n.val - 1 → depth b = n.val - 1 → lca a b = 1 →
        answerAt? r i = some (2 * n.val - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      depth a = n.val - 1 → depth b = n.val - 1 → lca a b = 1 →
        answerAt? r i = some (2 * n.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if lca(a_i,b_i) = 1 (the root), then r[i] = depth(a_i) + depth(b_i) + 1, where depth and lca are as in spec_1.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_13
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      lca a b = 1 → answerAt? r i = some (depth a + depth b + 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i : ℕ) (a b : ℤ), i < queries.val.length → queryAt? queries i = some (a, b) →
      lca a b = 1 → answerAt? r i = some (depth a + depth b + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0 <= i < m and 0 <= j < m, if a_i = a_j and b_i = b_j, then r[i] = r[j]. Thus equal queries receive equal answers.
  Preconditions: Let m = len(queries). Assume 2 <= n <= 30, 1 <= m <= 100000, and for every i with 0 <= i < m: queries[i] has length 2; writing a_i = queries[i][0] and b_i = queries[i][1], we have 1 <= a_i <= 2^n - 1, 1 <= b_i <= 2^n - 1, and a_i != b_i. -/
theorem spec_14
    (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r) :
    ∀ (i j : ℕ) (a b : ℤ), i < queries.val.length → j < queries.val.length →
      queryAt? queries i = some (a, b) → queryAt? queries j = some (a, b) →
        answerAt? r i = answerAt? r j := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 30)
    (hm_lo : 1 ≤ queries.val.length) (hm_hi : queries.val.length ≤ 100000)
    (hq : ∀ i : ℕ, i < queries.val.length → ∃ a b : ℤ,
      queryAt? queries i = some (a, b) ∧ 1 ≤ a ∧ a ≤ nodeBound n ∧ 1 ≤ b ∧ b ≤ nodeBound n ∧
        a ≠ b)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.CycleLengthQueries.cycle_length_queries n queries = ok r), ∀ (i j : ℕ) (a b : ℤ), i < queries.val.length → j < queries.val.length →
      queryAt? queries i = some (a, b) → queryAt? queries j = some (a, b) →
        answerAt? r i = answerAt? r j) := by
  sorry

end AegisSpec.CycleLengthQueries
