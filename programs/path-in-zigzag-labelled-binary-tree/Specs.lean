import Aegis.PathInZigZagTree.Code.Funs

/-!
# Specifications of `Aegis.PathInZigZagTree.path_in_zig_zag_tree`

LeetCode problem `path-in-zigzag-labelled-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PathInZigZagTree

def elem? (r : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ :=
  (r.val[i]?).map (fun x => x.val)

def elem (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ :=
  (elem? r i).getD 0

def vlen (r : alloc.vec.Vec Std.I64) : ℕ := r.val.length

def row (v : ℤ) : ℕ := v.toNat.log2 + 1

def pos (v : ℤ) : ℤ :=
  if row v % 2 = 1 then v - (2 : ℤ) ^ (row v - 1) else (2 : ℤ) ^ (row v) - 1 - v

def parent (v : ℤ) : ℤ :=
  if (row v - 1) % 2 = 1 then (2 : ℤ) ^ (row v - 2) + pos v / 2
  else (2 : ℤ) ^ (row v - 1) - 1 - pos v / 2

def iter (v : ℤ) : ℕ → ℤ
  | 0 => v
  | k + 1 => parent (iter v k)

/-- Let row(v) be the unique positive integer d with 2^(d-1) <= v < 2^d, and let pos(v) be the 0-based index of v from the left in its row: pos(v) = v - 2^(row(v)-1) when row(v) is odd, and pos(v) = 2^row(v) - 1 - v when row(v) is even. Let d = row(label) and p = pos(label). Whenever path_in_zig_zag_tree(label) returns a result r, len(r) = d and for every i with 0 <= i < d, r[i] = (2^i + floor(p / 2^(d-1-i))) if i+1 is odd, and r[i] = (2^(i+1) - 1 - floor(p / 2^(d-1-i))) if i+1 is even.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_1 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      vlen r = row label.val ∧
        ∀ i : ℕ, i < row label.val →
          elem r i =
            (if (i + 1) % 2 = 1 then
              (2 : ℤ) ^ i + pos label.val / (2 : ℤ) ^ (row label.val - 1 - i)
             else
              (2 : ℤ) ^ (i + 1) - 1 - pos label.val / (2 : ℤ) ^ (row label.val - 1 - i)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      vlen r = row label.val ∧
        ∀ i : ℕ, i < row label.val →
          elem r i =
            (if (i + 1) % 2 = 1 then
              (2 : ℤ) ^ i + pos label.val / (2 : ℤ) ^ (row label.val - 1 - i)
             else
              (2 : ℤ) ^ (i + 1) - 1 - pos label.val / (2 : ℤ) ^ (row label.val - 1 - i))) := by
  sorry

/-- For every i64 label with 1 <= label <= 10^6, path_in_zig_zag_tree(label) returns a result r; in particular, the computation does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_2 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∃ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∃ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r) := by
  sorry

/-- Let row(label) be the unique positive integer d with 2^(d-1) <= label < 2^d. Whenever path_in_zig_zag_tree(label) returns a result r, len(r) = row(label).
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_3 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      vlen r = row label.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      vlen r = row label.val) := by
  sorry

/-- Whenever path_in_zig_zag_tree(label) returns a result r, len(r) >= 1 and r[0] = 1.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_4 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      1 ≤ vlen r ∧ elem r 0 = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      1 ≤ vlen r ∧ elem r 0 = 1) := by
  sorry

/-- Whenever path_in_zig_zag_tree(label) returns a result r, len(r) >= 1 and r[len(r)-1] = label.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_5 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      1 ≤ vlen r ∧ elem r (vlen r - 1) = label.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      1 ≤ vlen r ∧ elem r (vlen r - 1) = label.val) := by
  sorry

/-- Let row(v) be the unique positive integer d with 2^(d-1) <= v < 2^d. Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < len(r), row(r[i]) = i+1.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_6 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → row (elem r i) = i + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → row (elem r i) = i + 1) := by
  sorry

/-- Let row(v) be the unique positive integer d with 2^(d-1) <= v < 2^d, and let pos(v) = v - 2^(row(v)-1) if row(v) is odd and pos(v) = 2^row(v) - 1 - v if row(v) is even, giving the 0-based left-to-right position of v in its row. Let d = row(label) and p = pos(label). Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < d, r has an i-th element and pos(r[i]) = floor(p / 2^(d-1-i)).
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_7 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < row label.val →
        ∃ x : ℤ, (elem? r i = some x) ∧
          pos x = pos label.val / (2 : ℤ) ^ (row label.val - 1 - i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < row label.val →
        ∃ x : ℤ, (elem? r i = some x) ∧
          pos x = pos label.val / (2 : ℤ) ^ (row label.val - 1 - i)) := by
  sorry

/-- Define row(v) as the unique positive integer e with 2^(e-1) <= v < 2^e, and pos(v) = v - 2^(row(v)-1) if row(v) is odd and pos(v) = 2^row(v) - 1 - v if row(v) is even. For v > 1, define parent(v) as the label in row row(v)-1 at 0-based position floor(pos(v)/2); explicitly, parent(v) = 2^(row(v)-2) + floor(pos(v)/2) if row(v)-1 is odd, and parent(v) = 2^(row(v)-1) - 1 - floor(pos(v)/2) if row(v)-1 is even. Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < len(r)-1, r[i] = parent(r[i+1]).
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_8 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r - 1 → elem r i = parent (elem r (i + 1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r - 1 → elem r i = parent (elem r (i + 1))) := by
  sorry

/-- Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < len(r)-1, r[i] < r[i+1].
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_9 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r - 1 → elem r i < elem r (i + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r - 1 → elem r i < elem r (i + 1)) := by
  sorry

/-- Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= label.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_10 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → 1 ≤ elem r i ∧ elem r i ≤ label.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → 1 ≤ elem r i ∧ elem r i ≤ label.val) := by
  sorry

/-- Define row(v) as the unique positive integer e with 2^(e-1) <= v < 2^e, and pos(v) = v - 2^(row(v)-1) if row(v) is odd and pos(v) = 2^row(v) - 1 - v if row(v) is even. For v > 1, let parent(v) be the label in row row(v)-1 at 0-based position floor(pos(v)/2). Let iter(v,0)=v and iter(v,k+1)=parent(iter(v,k)). Let d = row(label). Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < len(r), r[i] = iter(label, d-1-i).
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_11 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → elem r i = iter label.val (row label.val - 1 - i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → elem r i = iter label.val (row label.val - 1 - i)) := by
  sorry

/-- Whenever path_in_zig_zag_tree(label) returns a result r, for every i with 0 <= i < len(r), 2^i <= r[i] <= 2^(i+1) - 1.
  Preconditions: label is an i64 with 1 <= label <= 10^6. -/
theorem spec_12 (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6) :
    ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → (2 : ℤ) ^ i ≤ elem r i ∧ elem r i ≤ (2 : ℤ) ^ (i + 1) - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (label : Std.I64) (h1 : 1 ≤ label.val) (h2 : label.val ≤ 10 ^ 6), ∀ r, Aegis.PathInZigZagTree.path_in_zig_zag_tree label = ok r →
      ∀ i : ℕ, i < vlen r → (2 : ℤ) ^ i ≤ elem r i ∧ elem r i ≤ (2 : ℤ) ^ (i + 1) - 1) := by
  sorry

end AegisSpec.PathInZigZagTree
