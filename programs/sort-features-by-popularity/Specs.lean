import Aegis.SortFeatures.Code.Funs

/-!
# Specifications of `Aegis.SortFeatures.sort_features`

LeetCode problem `sort-features-by-popularity`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SortFeatures

abbrev Bytes : Type := List Std.U8

def space : Std.U8 := 32#u8

def entry (L : List (alloc.vec.Vec Std.U8)) (i : ℕ) : Bytes :=
  match L[i]? with
  | some v => v.val
  | none => []

def words (r : Bytes) : List Bytes := r.splitOn space

def occursAsWord (f r : Bytes) : Prop := f ≠ [] ∧ f ∈ words r

instance instDecidableOccursAsWord (f r : Bytes) : Decidable (occursAsWord f r) := by
  unfold occursAsWord
  infer_instance

noncomputable def wordCount (f r : Bytes) : ℕ := (words r).countP fun w => decide (w = f)

noncomputable def contribution (f r : Bytes) : ℕ := if occursAsWord f r then 1 else 0

noncomputable def pop (responses : Slice (alloc.vec.Vec Std.U8)) (f : Bytes) : ℕ :=
  (responses.val.filter fun v => decide (occursAsWord f v.val)).length

structure InputsValid (features responses : Slice (alloc.vec.Vec Std.U8)) : Prop where

  features_len_pos : 1 ≤ features.val.length

  features_len_le : features.val.length ≤ 10000

  features_entry_len : ∀ i, i < features.val.length →
    1 ≤ (entry features.val i).length ∧ (entry features.val i).length ≤ 10

  features_entry_bytes : ∀ i, i < features.val.length →
    ∀ b, b ∈ entry features.val i → 97 ≤ b.val ∧ b.val ≤ 122

  features_nodup : (features.val.map fun v => v.val).Nodup

  responses_len_pos : 1 ≤ responses.val.length

  responses_len_le : responses.val.length ≤ 100

  responses_entry_len : ∀ j, j < responses.val.length →
    1 ≤ (entry responses.val j).length ∧ (entry responses.val j).length ≤ 1000

  responses_entry_bytes : ∀ j, j < responses.val.length →
    ∀ b, b ∈ entry responses.val j → (97 ≤ b.val ∧ b.val ≤ 122) ∨ b.val = 32

  responses_no_leading_space : ∀ j, j < responses.val.length →
    (entry responses.val j)[0]? ≠ some space

  responses_no_trailing_space : ∀ j, j < responses.val.length →
    (entry responses.val j).getLast? ≠ some space

  responses_no_double_space : ∀ j, j < responses.val.length →
    ∀ i, i + 1 < (entry responses.val j).length →
      (entry responses.val j)[i]? = some space →
      (entry responses.val j)[i + 1]? ≠ some space

/-- Let pop(f), for any byte array f, be the number of indices j with 0 <= j < len(responses) such that f occurs as a space-delimited word in responses[j]; a space-delimited word is a maximal contiguous block of non-space bytes (32 is space), and if f occurs more than once in the same responses[j] it still contributes only 1. The function returns a result r such that: (1) len(r) = len(features); (2) for every j with 0 <= j < len(features) there is exactly one i with 0 <= i < len(r) for which r[i] is byte-for-byte equal to features[j]; and (3) for every i with 0 <= i+1 < len(r), either pop(r[i]) > pop(r[i+1]), or pop(r[i]) = pop(r[i+1]) and the unique index j with r[i] = features[j] is less than the unique index k with r[i+1] = features[k].
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_1 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r ∧
      r.val.length = features.val.length ∧
      (∀ j, j < features.val.length →
        ∃! i, i < r.val.length ∧ entry r.val i = entry features.val j) ∧
      (∀ i, i + 1 < r.val.length →
        pop responses (entry r.val i) > pop responses (entry r.val (i + 1)) ∨
        (pop responses (entry r.val i) = pop responses (entry r.val (i + 1)) ∧
          ∃ j k, j < features.val.length ∧ k < features.val.length ∧
            entry features.val j = entry r.val i ∧
            entry features.val k = entry r.val (i + 1) ∧ j < k)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r ∧
      r.val.length = features.val.length ∧
      (∀ j, j < features.val.length →
        ∃! i, i < r.val.length ∧ entry r.val i = entry features.val j) ∧
      (∀ i, i + 1 < r.val.length →
        pop responses (entry r.val i) > pop responses (entry r.val (i + 1)) ∨
        (pop responses (entry r.val i) = pop responses (entry r.val (i + 1)) ∧
          ∃ j k, j < features.val.length ∧ k < features.val.length ∧
            entry features.val j = entry r.val i ∧
            entry features.val k = entry r.val (i + 1) ∧ j < k))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index on any input satisfying the preconditions.
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_2 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every byte array x, the number of indices i with 0 <= i < len(r) and r[i] byte-for-byte equal to x equals the number of indices j with 0 <= j < len(features) and features[j] byte-for-byte equal to x.
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_3 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ x : Bytes,
        (r.val.filter fun v => decide (v.val = x)).length =
        (features.val.filter fun v => decide (v.val = x)).length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ x : Bytes,
        (r.val.filter fun v => decide (v.val = x)).length =
        (features.val.filter fun v => decide (v.val = x)).length) := by
  sorry

/-- Whenever the function returns a result r, for every output position i with 0 <= i < len(r) and every response index j with 0 <= j < len(responses), if r[i] occurs as a space-delimited word in responses[j], then responses[j] contributes exactly 1 to the popularity of r[i], even if r[i] occurs two or more times as a word in responses[j]; it never contributes more than 1 from the same response.
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_4 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i, i < r.val.length →
      ∀ j, j < responses.val.length →
        occursAsWord (entry r.val i) (entry responses.val j) →
          contribution (entry r.val i) (entry responses.val j) = 1 ∧
          1 ≤ wordCount (entry r.val i) (entry responses.val j) ∧
          contribution (entry r.val i) (entry responses.val j) ≤ 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i, i < r.val.length →
      ∀ j, j < responses.val.length →
        occursAsWord (entry r.val i) (entry responses.val j) →
          contribution (entry r.val i) (entry responses.val j) = 1 ∧
          1 ≤ wordCount (entry r.val i) (entry responses.val j) ∧
          contribution (entry r.val i) (entry responses.val j) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, for every output position i with 0 <= i < len(r) and every response index j with 0 <= j < len(responses), responses[j] contributes to the popularity of r[i] if and only if r[i] is byte-for-byte equal to one complete space-delimited word of responses[j], where a word is a maximal contiguous block of bytes different from space (32). In particular, an occurrence of r[i] only as a proper contiguous substring of a longer word (for example 'lock' inside 'locker') contributes 0.
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_5 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i, i < r.val.length →
      ∀ j, j < responses.val.length →
        (contribution (entry r.val i) (entry responses.val j) = 1 ↔
          occursAsWord (entry r.val i) (entry responses.val j)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i, i < r.val.length →
      ∀ j, j < responses.val.length →
        (contribution (entry r.val i) (entry responses.val j) = 1 ↔
          occursAsWord (entry r.val i) (entry responses.val j))) := by
  sorry

/-- Whenever the function returns a result r, for every pair i,k with 0 <= i < k < len(r), pop(r[i]) >= pop(r[k]), where pop(f) for a byte array f is the number of indices j with 0 <= j < len(responses) such that f occurs as a space-delimited word in responses[j] (repeated occurrences in one response count once).
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_6 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i k, i < k → k < r.val.length →
        pop responses (entry r.val i) ≥ pop responses (entry r.val k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i k, i < k → k < r.val.length →
        pop responses (entry r.val i) ≥ pop responses (entry r.val k)) := by
  sorry

/-- Whenever the function returns a result r, for every pair i,k with 0 <= i < k < len(r), if pop(r[i]) = pop(r[k]), then the unique index j with 0 <= j < len(features) and features[j] = r[i] is less than the unique index l with 0 <= l < len(features) and features[l] = r[k], where pop(f) is the number of responses containing f as a space-delimited word (repeated occurrences in one response count once).
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_7 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i k, i < k → k < r.val.length →
        pop responses (entry r.val i) = pop responses (entry r.val k) →
          ∃ j l, j < features.val.length ∧ l < features.val.length ∧
            entry features.val j = entry r.val i ∧
            entry features.val l = entry r.val k ∧ j < l := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      ∀ i k, i < k → k < r.val.length →
        pop responses (entry r.val i) = pop responses (entry r.val k) →
          ∃ j l, j < features.val.length ∧ l < features.val.length ∧
            entry features.val j = entry r.val i ∧
            entry features.val l = entry r.val k ∧ j < l) := by
  sorry

/-- Whenever the function returns Ok r and len(r) > 0, there exists p with 0 <= p < len(features) such that features[p] = r[0], and for every j with 0 <= j < len(features), pop(r[0]) >= pop(features[j]) and (if pop(features[j]) = pop(r[0]) then p <= j), where pop(f) is the number of responses containing f as a space-delimited word (repeated occurrences in one response count once).
  Preconditions: features is a slice of byte-array strings and responses is a slice of byte-array strings. 1 <= len(features) <= 10^4. For every i with 0 <= i < len(features), 1 <= len(features[i]) <= 10, every byte of features[i] is an ASCII lowercase letter (97..122), and no two entries of features are equal as byte arrays. 1 <= len(responses) <= 10^2. For every j with 0 <= j < len(responses), 1 <= len(responses[j]) <= 10^3, every byte of responses[j] is either an ASCII lowercase letter or a space (32), responses[j] has no leading space, no trailing space, and no two consecutive spaces. -/
theorem spec_8 (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      0 < r.val.length →
        ∃ p, p < features.val.length ∧ entry features.val p = entry r.val 0 ∧
          (∀ j, j < features.val.length →
            pop responses (entry r.val 0) ≥ pop responses (entry features.val j) ∧
            (pop responses (entry features.val j) = pop responses (entry r.val 0) → p ≤ j)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (features responses : Slice (alloc.vec.Vec Std.U8))
    (h : InputsValid features responses), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.SortFeatures.sort_features features responses = ok r →
      0 < r.val.length →
        ∃ p, p < features.val.length ∧ entry features.val p = entry r.val 0 ∧
          (∀ j, j < features.val.length →
            pop responses (entry r.val 0) ≥ pop responses (entry features.val j) ∧
            (pop responses (entry features.val j) = pop responses (entry r.val 0) → p ≤ j))) := by
  sorry

end AegisSpec.SortFeatures
