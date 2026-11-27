import Aegis.MaximumBeauty.Code.Funs

/-!
# Specifications of `Aegis.MaximumBeauty.maximum_beauty`

LeetCode problem `most-beautiful-item-for-each-query`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumBeauty

open Aegis.MaximumBeauty (maximum_beauty)

def itemAt (items : Slice (alloc.vec.Vec I64)) (i : ℕ) : Option (ℤ × ℤ) :=
  match items.val[i]? with
  | none => none
  | some v =>
    match v.val with
    | [p, b] => some (p.val, b.val)
    | _ => none

def affordableBeauties (items : Slice (alloc.vec.Vec I64)) (q : ℤ) : List ℤ :=
  (List.range items.val.length).filterMap fun i =>
    match itemAt items i with
    | some (p, b) => if p ≤ q then some b else none
    | none => none

def allBeauties (items : Slice (alloc.vec.Vec I64)) : List ℤ :=
  (List.range items.val.length).filterMap fun i => (itemAt items i).map (fun pb => pb.2)

def bestBeauty (items : Slice (alloc.vec.Vec I64)) (q : ℤ) : ℤ :=
  (affordableBeauties items q).max?.getD 0

def maxBeauty (items : Slice (alloc.vec.Vec I64)) : Option ℤ :=
  (allBeauties items).max?

def HasAffordable (items : Slice (alloc.vec.Vec I64)) (q : ℤ) : Prop :=
  ∃ i p b, i < items.val.length ∧ itemAt items i = some (p, b) ∧ p ≤ q

def outVal (r : alloc.vec.Vec I64) (j : ℕ) : Option ℤ := (r.val[j]?).map (fun x => x.val)

def ItemsPre (items : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ items.val.length ∧ items.val.length ≤ 100000 ∧
    ∀ i, i < items.val.length →
      ∃ p b, itemAt items i = some (p, b) ∧ 1 ≤ p ∧ p ≤ 10 ^ 9 ∧ 1 ≤ b ∧ b ≤ 10 ^ 9

def QueriesPre (queries : Slice I64) : Prop :=
  1 ≤ queries.val.length ∧ queries.val.length ≤ 100000 ∧
    ∀ j (h : j < queries.val.length), 1 ≤ (queries.val[j]'h).val

/-- Whenever the function returns a result r, then for every j with 0 <= j < len(queries): if the set E_j = { items[i][1] | 0 <= i < len(items) and items[i][0] <= queries[j] } is non-empty, r[j] = max(E_j); and if E_j is empty, r[j] = 0.
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. (items[i][0] is the price and items[i][1] is the beauty of item i.) -/
theorem spec_1 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length),
      outVal r j = some (bestBeauty items (queries.val[j]'hj).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length),
      outVal r j = some (bestBeauty items (queries.val[j]'hj).val)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(queries).
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_2 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    r.val.length = queries.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), r.val.length = queries.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), 0 <= r[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_3 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x → 0 ≤ x := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x → 0 ≤ x) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), r[j] <= 10^9.
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_4 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x → x ≤ 10 ^ 9 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x → x ≤ 10 ^ 9) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries): if there exists i with 0 <= i < len(items) and items[i][0] <= queries[j], then there exists such an i with items[i][1] = r[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_5 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x →
      HasAffordable items (queries.val[j]'hj).val →
      ∃ i p, i < items.val.length ∧ itemAt items i = some (p, x) ∧
        p ≤ (queries.val[j]'hj).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x →
      HasAffordable items (queries.val[j]'hj).val →
      ∃ i p, i < items.val.length ∧ itemAt items i = some (p, x) ∧
        p ≤ (queries.val[j]'hj).val) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries) and every i with 0 <= i < len(items): if items[i][0] <= queries[j] then items[i][1] <= r[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_6 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length), ∀ i p b, i < items.val.length →
      itemAt items i = some (p, b) → p ≤ (queries.val[j]'hj).val →
      ∀ x, outVal r j = some x → b ≤ x := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length), ∀ i p b, i < items.val.length →
      itemAt items i = some (p, b) → p ≤ (queries.val[j]'hj).val →
      ∀ x, outVal r j = some x → b ≤ x) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries): if for every i with 0 <= i < len(items), queries[j] < items[i][0], then r[j] = 0.
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_7 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length),
      (∀ i p b, i < items.val.length → itemAt items i = some (p, b) →
          (queries.val[j]'hj).val < p) →
      outVal r j = some 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length),
      (∀ i p b, i < items.val.length → itemAt items i = some (p, b) →
          (queries.val[j]'hj).val < p) →
      outVal r j = some 0) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries): r[j] = 0 if and only if there is no i with 0 <= i < len(items) and items[i][0] <= queries[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_8 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length),
      (outVal r j = some 0 ↔ ¬ HasAffordable items (queries.val[j]'hj).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length),
      (outVal r j = some 0 ↔ ¬ HasAffordable items (queries.val[j]'hj).val)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries): if queries[j] >= items[i][0] for every i with 0 <= i < len(items), then r[j] = max{ items[i][1] | 0 <= i < len(items) }.
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_9 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length),
      (∀ i p b, i < items.val.length → itemAt items i = some (p, b) →
          p ≤ (queries.val[j]'hj).val) →
      outVal r j = maxBeauty items := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length),
      (∀ i p b, i < items.val.length → itemAt items i = some (p, b) →
          p ≤ (queries.val[j]'hj).val) →
      outVal r j = maxBeauty items) := by
  sorry

/-- Whenever the function returns a result r, for all j1, j2 with 0 <= j1 < len(queries) and 0 <= j2 < len(queries): if queries[j1] <= queries[j2], then r[j1] <= r[j2].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_10 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j1 (h1 : j1 < queries.val.length) (j2 : ℕ) (h2 : j2 < queries.val.length),
      (queries.val[j1]'h1).val ≤ (queries.val[j2]'h2).val →
      ∀ x y, outVal r j1 = some x → outVal r j2 = some y → x ≤ y := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j1 (h1 : j1 < queries.val.length) (j2 : ℕ) (h2 : j2 < queries.val.length),
      (queries.val[j1]'h1).val ≤ (queries.val[j2]'h2).val →
      ∀ x y, outVal r j1 = some x → outVal r j2 = some y → x ≤ y) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), either r[j] = 0, or there exists i with 0 <= i < len(items) and items[i][1] = r[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_11 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r) :
    ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x →
      x = 0 ∨ ∃ i p, i < items.val.length ∧ itemAt items i = some (p, x) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries)
    (r : alloc.vec.Vec I64) (hres : maximum_beauty items queries = ok r), ∀ j (hj : j < queries.val.length), ∀ x, outVal r j = some x →
      x = 0 ∨ ∃ i p, i < items.val.length ∧ itemAt items i = some (p, x)) := by
  sorry

/-- If the function returns r on (items, queries) and returns r2 on (items2, queries), then for every j with 0 <= j < len(queries), r2[j] = r[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. In the statement, items2 is any slice of Vec I64 satisfying the same preconditions whose elements are a permutation of the elements of items (in particular len(items2) = len(items)). -/
theorem spec_12 (items items2 : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_items2 : ItemsPre items2) (h_queries : QueriesPre queries)
    (hperm : items2.val.Perm items.val)
    (r r2 : alloc.vec.Vec I64)
    (hres : maximum_beauty items queries = ok r)
    (hres2 : maximum_beauty items2 queries = ok r2) :
    ∀ j (hj : j < queries.val.length), outVal r2 j = outVal r j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (items items2 : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_items2 : ItemsPre items2) (h_queries : QueriesPre queries)
    (hperm : items2.val.Perm items.val)
    (r r2 : alloc.vec.Vec I64)
    (hres : maximum_beauty items queries = ok r)
    (hres2 : maximum_beauty items2 queries = ok r2), ∀ j (hj : j < queries.val.length), outVal r2 j = outVal r j) := by
  sorry

/-- The function returns a result r: for every input satisfying the preconditions it does not panic, overflow, or index out of bounds.
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. -/
theorem spec_13 (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries) :
    ∃ r, maximum_beauty items queries = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (items : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_queries : QueriesPre queries), ∃ r, maximum_beauty items queries = ok r) := by
  sorry

/-- If the function returns r on (items, queries) and returns r2 on (items2, queries), then for every j with 0 <= j < len(queries), r[j] <= r2[j].
  Preconditions: 1 <= len(items) <= 100000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(items): len(items[i]) = 2, 1 <= items[i][0] <= 10^9 and 1 <= items[i][1] <= 10^9; for every j with 0 <= j < len(queries): queries[j] >= 1. In the statement, items2 is any slice of Vec I64 satisfying the same preconditions and some i0 with 0 <= i0 < len(items) such that items2 has the same length as items, items2[i0][0] = items[i0][0], items[i0][1] <= items2[i0][1], and items2[i] = items[i] for every i with i != i0. -/
theorem spec_14 (items items2 : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_items2 : ItemsPre items2) (h_queries : QueriesPre queries)
    (i0 : ℕ) (hi0 : i0 < items.val.length)
    (hlen : items2.val.length = items.val.length)
    (hprice : ∀ p b2, itemAt items2 i0 = some (p, b2) →
      ∃ b, itemAt items i0 = some (p, b) ∧ b ≤ b2)
    (hother : ∀ i, i ≠ i0 → items2.val[i]? = items.val[i]?)
    (r r2 : alloc.vec.Vec I64)
    (hres : maximum_beauty items queries = ok r)
    (hres2 : maximum_beauty items2 queries = ok r2) :
    ∀ j (hj : j < queries.val.length), ∀ x y,
      outVal r j = some x → outVal r2 j = some y → x ≤ y := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (items items2 : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
    (h_items : ItemsPre items) (h_items2 : ItemsPre items2) (h_queries : QueriesPre queries)
    (i0 : ℕ) (hi0 : i0 < items.val.length)
    (hlen : items2.val.length = items.val.length)
    (hprice : ∀ p b2, itemAt items2 i0 = some (p, b2) →
      ∃ b, itemAt items i0 = some (p, b) ∧ b ≤ b2)
    (hother : ∀ i, i ≠ i0 → items2.val[i]? = items.val[i]?)
    (r r2 : alloc.vec.Vec I64)
    (hres : maximum_beauty items queries = ok r)
    (hres2 : maximum_beauty items2 queries = ok r2), ∀ j (hj : j < queries.val.length), ∀ x y,
      outVal r j = some x → outVal r2 j = some y → x ≤ y) := by
  sorry

end AegisSpec.MaximumBeauty
