import Aegis.ValidUtf8.Code.Funs

/-!
# Specifications of `Aegis.ValidUtf8.valid_utf8`

LeetCode problem `utf-8-validation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ValidUtf8

namespace AegisSpec.ValidUtf8

def bytes (data : Slice Std.I64) : List ℤ := data.val.map (fun b => b.val)

def IsSingleChar : List ℤ → Prop
  | [b] => 0 ≤ b ∧ b < 128
  | [b, c1] => 192 ≤ b ∧ b < 224 ∧ 128 ≤ c1 ∧ c1 < 192
  | [b, c1, c2] => 224 ≤ b ∧ b < 240 ∧ 128 ≤ c1 ∧ c1 < 192 ∧ 128 ≤ c2 ∧ c2 < 192
  | [b, c1, c2, c3] =>
      240 ≤ b ∧ b < 248 ∧ 128 ≤ c1 ∧ c1 < 192 ∧ 128 ≤ c2 ∧ c2 < 192 ∧ 128 ≤ c3 ∧
        c3 < 192
  | _ => False

def IsValidUtf8 : List ℤ → Prop
  | [] => True
  | b :: rest =>
      if b < 128 then
        IsValidUtf8 rest
      else if 192 ≤ b ∧ b < 224 then
        (match rest with
         | c1 :: rest' => 128 ≤ c1 ∧ c1 < 192 ∧ IsValidUtf8 rest'
         | [] => False)
      else if 224 ≤ b ∧ b < 240 then
        (match rest with
         | c1 :: c2 :: rest' =>
             128 ≤ c1 ∧ c1 < 192 ∧ 128 ≤ c2 ∧ c2 < 192 ∧ IsValidUtf8 rest'
         | _ => False)
      else if 240 ≤ b ∧ b < 248 then
        (match rest with
         | c1 :: c2 :: c3 :: rest' =>
             128 ≤ c1 ∧ c1 < 192 ∧ 128 ≤ c2 ∧ c2 < 192 ∧ 128 ≤ c3 ∧ c3 < 192 ∧
               IsValidUtf8 rest'
         | _ => False)
      else
        False

def ValidUtf8From (bs : List ℤ) (i : ℕ) : Prop := IsValidUtf8 (bs.drop i)

def IsConcatOfChars (bs : List ℤ) : Prop :=
  ∃ cs : List (List ℤ), cs ≠ [] ∧ (∀ c ∈ cs, IsSingleChar c) ∧ cs.flatten = bs

def countBetween (lo hi : ℤ) (bs : List ℤ) : ℕ :=
  bs.countP (fun x => decide (lo ≤ x ∧ x < hi))

/-- The function returns a result r (it does not fail) and r = true if and only if data[0..len(data)-1] is a valid UTF-8 encoding. A valid UTF-8 encoding is a concatenation of one or more UTF-8 characters, where a UTF-8 character is exactly one of: (1) a single byte b with 0 <= b < 128; (2) a byte b with 192 <= b < 224 followed by exactly one byte c with 128 <= c < 192; (3) a byte b with 224 <= b < 240 followed by exactly two bytes c1, c2 with 128 <= c1 < 192 and 128 <= c2 < 192; (4) a byte b with 240 <= b < 248 followed by exactly three bytes c1, c2, c3 with 128 <= c1 < 192, 128 <= c2 < 192, and 128 <= c3 < 192. No other bytes may appear, and the concatenation must cover the entire array (the characters partition data in order). Equivalently, r = true iff the recursive predicate valid(data, 0) is true, where valid(data, i) is true if i = len(data), and otherwise: if data[i] < 128 then valid(data, i+1); if 192 <= data[i] < 224 then i+1 < len(data) and 128 <= data[i+1] < 192 and valid(data, i+2); if 224 <= data[i] < 240 then i+2 < len(data) and 128 <= data[i+1] < 192 and 128 <= data[i+2] < 192 and valid(data, i+3); if 240 <= data[i] < 248 then i+3 < len(data) and 128 <= data[i+1] < 192 and 128 <= data[i+2] < 192 and 128 <= data[i+3] < 192 and valid(data, i+4); otherwise false.
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_1 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    ∃ r, valid_utf8 data = ok r ∧ (r = true ↔ ValidUtf8From (bytes data) 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), ∃ r, valid_utf8 data = ok r ∧ (r = true ↔ ValidUtf8From (bytes data) 0)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_2 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    ∃ r, valid_utf8 data = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), ∃ r, valid_utf8 data = ok r) := by
  sorry

/-- The function returns true.
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] < 128. -/
theorem spec_3 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_ascii : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! < 128) :
    ∃ r, valid_utf8 data = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_ascii : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! < 128), ∃ r, valid_utf8 data = ok r ∧ r = true) := by
  sorry

/-- The function returns false.
  Preconditions: 1 <= len(data) <= 20000, for every i with 0 <= i < len(data), 0 <= data[i] <= 255, and 128 <= data[0] < 192. -/
theorem spec_4 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_first : 128 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 192) :
    ∃ r, valid_utf8 data = ok r ∧ r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_first : 128 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 192), ∃ r, valid_utf8 data = ok r ∧ r = false) := by
  sorry

/-- If the function returns true, then data[len(data)-1] < 192.
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_5 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    valid_utf8 data = ok true → (bytes data)[data.length - 1]! < 192 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), valid_utf8 data = ok true → (bytes data)[data.length - 1]! < 192) := by
  sorry

/-- If the function returns true, then either data[0] < 128 or 192 <= data[0] < 248.
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_6 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    valid_utf8 data = ok true →
      ((bytes data)[0]! < 128 ∨ (192 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 248)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), valid_utf8 data = ok true →
      ((bytes data)[0]! < 128 ∨ (192 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 248))) := by
  sorry

/-- When both calls return results r1 and r2, valid_utf8(c ++ data) and valid_utf8(data) have the same result (r1 = r2).
  Preconditions: For some k in {1,2,3,4}, c is a sequence of length k that is a single valid UTF-8 character (k=1: 0 <= c[0] < 128; k=2: 192 <= c[0] < 224 and 128 <= c[1] < 192; k=3: 224 <= c[0] < 240 and 128 <= c[1],c[2] < 192; k=4: 240 <= c[0] < 248 and 128 <= c[1],c[2],c[3] < 192), 1 <= len(data) <= 20000 - k, and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_7 (c data : Slice Std.I64) (k : ℕ)
    (h_k : k = c.length) (h_k_ge : 1 ≤ k) (h_k_le : k ≤ 4)
    (h_char : IsSingleChar (bytes c))
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000 - k)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_concat_bound : (c.val ++ data.val).length ≤ Std.Usize.max) :
    ∃ r1 r2,
      valid_utf8 (Slice.from (c.val ++ data.val) h_concat_bound) = ok r1 ∧
        valid_utf8 data = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (c data : Slice Std.I64) (k : ℕ)
    (h_k : k = c.length) (h_k_ge : 1 ≤ k) (h_k_le : k ≤ 4)
    (h_char : IsSingleChar (bytes c))
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000 - k)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_concat_bound : (c.val ++ data.val).length ≤ Std.Usize.max), ∃ r1 r2,
      valid_utf8 (Slice.from (c.val ++ data.val) h_concat_bound) = ok r1 ∧
        valid_utf8 data = ok r2 ∧ r1 = r2) := by
  sorry

/-- When both calls return results r1 and r2, valid_utf8(data ++ [b]) and valid_utf8(data) have the same result (r1 = r2).
  Preconditions: 1 <= len(data) <= 19999, for every i with 0 <= i < len(data), 0 <= data[i] <= 255, and 0 <= b < 128. -/
theorem spec_8 (data : Slice Std.I64) (b : Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 19999)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_b : 0 ≤ b.val ∧ b.val < 128)
    (h_concat_bound : (data.val ++ [b]).length ≤ Std.Usize.max) :
    ∃ r1 r2,
      valid_utf8 (Slice.from (data.val ++ [b]) h_concat_bound) = ok r1 ∧
        valid_utf8 data = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (data : Slice Std.I64) (b : Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 19999)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_b : 0 ≤ b.val ∧ b.val < 128)
    (h_concat_bound : (data.val ++ [b]).length ≤ Std.Usize.max), ∃ r1 r2,
      valid_utf8 (Slice.from (data.val ++ [b]) h_concat_bound) = ok r1 ∧
        valid_utf8 data = ok r2 ∧ r1 = r2) := by
  sorry

/-- The function returns a result r and r = true if and only if there exist an integer k >= 1 and indices 0 = i_0 < i_1 < ... < i_k = len(data) such that for every j with 1 <= j <= k, the block data[i_{j-1}..i_j-1] is a valid UTF-8 character (as defined in spec_1). In other words, r = true iff data can be partitioned into a sequence of valid UTF-8 characters covering exactly all elements.
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_9 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    ∃ r, valid_utf8 data = ok r ∧ (r = true ↔ IsConcatOfChars (bytes data)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), ∃ r, valid_utf8 data = ok r ∧ (r = true ↔ IsConcatOfChars (bytes data))) := by
  sorry

/-- Let L2 = #{i | 0 <= i < len(data) and 192 <= data[i] < 224}, L3 = #{i | 0 <= i < len(data) and 224 <= data[i] < 240}, L4 = #{i | 0 <= i < len(data) and 240 <= data[i] < 248}, and C = #{i | 0 <= i < len(data) and 128 <= data[i] < 192}. If the function returns true, then C = L2 + 2*L3 + 3*L4.
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_10 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    valid_utf8 data = ok true →
      countBetween 128 192 (bytes data) =
        countBetween 192 224 (bytes data) + 2 * countBetween 224 240 (bytes data) +
          3 * countBetween 240 248 (bytes data) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), valid_utf8 data = ok true →
      countBetween 128 192 (bytes data) =
        countBetween 192 224 (bytes data) + 2 * countBetween 224 240 (bytes data) +
          3 * countBetween 240 248 (bytes data)) := by
  sorry

/-- The function returns true if and only if for every i with 1 <= i < n, 128 <= data[i] < 192.
  Preconditions: Let n = len(data). Then n is in {1,2,3,4}, for every i with 0 <= i < n, 0 <= data[i] <= 255, and data[0] is an n-byte leading byte: 0 <= data[0] < 128 if n=1, 192 <= data[0] < 224 if n=2, 224 <= data[0] < 240 if n=3, and 240 <= data[0] < 248 if n=4. -/
theorem spec_11 (data : Slice Std.I64) (n : ℕ)
    (h_n : n = data.length)
    (h_n_mem : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4)
    (h_byte_range : ∀ i : ℕ, i < n → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_lead :
      (n = 1 ∧ 0 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 128) ∨
      (n = 2 ∧ 192 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 224) ∨
      (n = 3 ∧ 224 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 240) ∨
      (n = 4 ∧ 240 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 248)) :
    ∃ r,
      valid_utf8 data = ok r ∧
        (r = true ↔ ∀ i : ℕ, 1 ≤ i → i < n → 128 ≤ (bytes data)[i]! ∧ (bytes data)[i]! < 192) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (data : Slice Std.I64) (n : ℕ)
    (h_n : n = data.length)
    (h_n_mem : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4)
    (h_byte_range : ∀ i : ℕ, i < n → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255)
    (h_lead :
      (n = 1 ∧ 0 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 128) ∨
      (n = 2 ∧ 192 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 224) ∨
      (n = 3 ∧ 224 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 240) ∨
      (n = 4 ∧ 240 ≤ (bytes data)[0]! ∧ (bytes data)[0]! < 248)), ∃ r,
      valid_utf8 data = ok r ∧
        (r = true ↔ ∀ i : ℕ, 1 ≤ i → i < n → 128 ≤ (bytes data)[i]! ∧ (bytes data)[i]! < 192)) := by
  sorry

/-- If the function returns true, then for every i with 0 <= i <= len(data) such that the prefix data[0..i-1] is a valid UTF-8 encoding (using the definition from spec_1, with the empty prefix being valid), the suffix data[i..len(data)-1] is also a valid UTF-8 encoding (with the empty suffix being valid).
  Preconditions: 1 <= len(data) <= 20000 and for every i with 0 <= i < len(data), 0 <= data[i] <= 255. -/
theorem spec_12 (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255) :
    valid_utf8 data = ok true →
      ∀ i : ℕ, i ≤ data.length → IsValidUtf8 ((bytes data).take i) →
        IsValidUtf8 ((bytes data).drop i) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (data : Slice Std.I64)
    (h_len_ge : 1 ≤ data.length) (h_len_le : data.length ≤ 20000)
    (h_byte_range : ∀ i : ℕ, i < data.length → 0 ≤ (bytes data)[i]! ∧ (bytes data)[i]! ≤ 255), valid_utf8 data = ok true →
      ∀ i : ℕ, i ≤ data.length → IsValidUtf8 ((bytes data).take i) →
        IsValidUtf8 ((bytes data).drop i)) := by
  sorry

end AegisSpec.ValidUtf8
