import Aegis.RearrangeCharacters.Code.Funs

/-!
# Specifications of `Aegis.RearrangeCharacters.rearrange_characters`

LeetCode problem `rearrange-characters-to-make-target-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RearrangeCharacters

def count (x : Slice Std.U8) (c : Std.U8) : Nat :=
  x.val.countP fun b => b == c

def IsLower (x : Slice Std.U8) : Prop :=
  ∀ b ∈ x.val, 97 ≤ b.val ∧ b.val ≤ 122

def Packing (s target : Slice Std.U8) (k : Nat) : Prop :=
  ∃ I : Fin k → Finset (Fin s.val.length),
    (∀ j, (I j).card = target.val.length) ∧
    (∀ j, (I j).val.map (fun i => s.val.get i) = (target.val : Multiset Std.U8)) ∧
    (∀ j j', j ≠ j' → Disjoint (I j) (I j'))

/-- The function returns a result r, and r is the greatest integer k with k >= 0 such that for every byte c, k * count(target,c) <= count(s,c). Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_1 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target) :
    ∃ r : Std.I64,
      Aegis.RearrangeCharacters.rearrange_characters s target = ok r ∧
      0 ≤ r.val ∧
      (∀ c : Std.U8, r.val * (count target c : Int) ≤ (count s c : Int)) ∧
      (∀ k : Int, 0 ≤ k →
        (∀ c : Std.U8, k * (count target c : Int) ≤ (count s c : Int)) → k ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target), ∃ r : Std.I64,
      Aegis.RearrangeCharacters.rearrange_characters s target = ok r ∧
      0 ≤ r.val ∧
      (∀ c : Std.U8, r.val * (count target c : Int) ≤ (count s c : Int)) ∧
      (∀ k : Int, 0 ≤ k →
        (∀ c : Std.U8, k * (count target c : Int) ≤ (count s c : Int)) → k ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r and r <= len(s) / len(target), where / is integer division (floor for non-negative integers).
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_2 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((s.val.length / target.val.length : Nat) : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), 0 ≤ r.val ∧ r.val ≤ ((s.val.length / target.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every byte c with count(target,c) > 0, r * count(target,c) <= count(s,c). Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_3 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ c : Std.U8, 0 < count target c → r.val * (count target c : Int) ≤ (count s c : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ c : Std.U8, 0 < count target c → r.val * (count target c : Int) ≤ (count s c : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a byte c such that count(target,c) > 0 and count(s,c) < count(target,c). Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_4 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    r.val = 0 ↔ ∃ c : Std.U8, 0 < count target c ∧ count s c < count target c := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), r.val = 0 ↔ ∃ c : Std.U8, 0 < count target c ∧ count s c < count target c) := by
  sorry

/-- Whenever the function returns a result r, r = count(s,c) / len(target), where c is the byte with target[i] = c for all i, and / is integer division. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122), and there is a byte c such that target[i] = c for every i with 0 <= i < len(target). -/
theorem spec_5 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (c : Std.U8) (h_c : ∀ b ∈ target.val, b = c)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    r.val = ((count s c / target.val.length : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (c : Std.U8) (h_c : ∀ b ∈ target.val, b = c)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), r.val = ((count s c / target.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every slice s' of bytes such that 1 <= len(s') <= 100, every byte of s' is an ASCII lowercase letter, and count(s',c) = count(s,c) for every byte c, the call rearrange_characters(s', target) returns a result equal to r. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_6 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
      (∀ c : Std.U8, count s' c = count s c) →
      Aegis.RearrangeCharacters.rearrange_characters s' target = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
      (∀ c : Std.U8, count s' c = count s c) →
      Aegis.RearrangeCharacters.rearrange_characters s' target = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every slice target' of bytes such that 1 <= len(target') <= 10, every byte of target' is an ASCII lowercase letter, and count(target',c) = count(target,c) for every byte c, the call rearrange_characters(s, target') returns a result equal to r. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_7 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ target' : Slice Std.U8, 1 ≤ target'.val.length → target'.val.length ≤ 10 →
      IsLower target' →
      (∀ c : Std.U8, count target' c = count target c) →
      Aegis.RearrangeCharacters.rearrange_characters s target' = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ target' : Slice Std.U8, 1 ≤ target'.val.length → target'.val.length ≤ 10 →
      IsLower target' →
      (∀ c : Std.U8, count target' c = count target c) →
      Aegis.RearrangeCharacters.rearrange_characters s target' = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every slice s' of bytes such that 1 <= len(s') <= 100, every byte of s' is an ASCII lowercase letter, and count(s',c) >= count(s,c) for every byte c, the call rearrange_characters(s', target) returns a result r' with r' >= r. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_8 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
      (∀ c : Std.U8, count s c ≤ count s' c) →
      ∃ r' : Std.I64,
        Aegis.RearrangeCharacters.rearrange_characters s' target = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
      (∀ c : Std.U8, count s c ≤ count s' c) →
      ∃ r' : Std.I64,
        Aegis.RearrangeCharacters.rearrange_characters s' target = ok r' ∧ r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, for every slice target' of bytes such that 1 <= len(target') <= 10, every byte of target' is an ASCII lowercase letter, and count(target',c) >= count(target,c) for every byte c, the call rearrange_characters(s, target') returns a result r' with r' <= r. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_9 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ target' : Slice Std.U8, 1 ≤ target'.val.length → target'.val.length ≤ 10 →
      IsLower target' →
      (∀ c : Std.U8, count target c ≤ count target' c) →
      ∃ r' : Std.I64,
        Aegis.RearrangeCharacters.rearrange_characters s target' = ok r' ∧ r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ target' : Slice Std.U8, 1 ≤ target'.val.length → target'.val.length ≤ 10 →
      IsLower target' →
      (∀ c : Std.U8, count target c ≤ count target' c) →
      ∃ r' : Std.I64,
        Aegis.RearrangeCharacters.rearrange_characters s target' = ok r' ∧ r'.val ≤ r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, or panic.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_10 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target) :
    ∃ r : Std.I64, Aegis.RearrangeCharacters.rearrange_characters s target = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target), ∃ r : Std.I64, Aegis.RearrangeCharacters.rearrange_characters s target = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k <= r there exist pairwise disjoint sets I_1, ..., I_k of indices of s such that for every j with 1 <= j <= k, len(I_j) = len(target) and the multiset of bytes {s[i] | i in I_j} is equal to the multiset of bytes {target[i] | 0 <= i < len(target)}. For k = 0 the family of sets is empty.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_11 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ k : Nat, (k : Int) ≤ r.val → Packing s target k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ k : Nat, (k : Int) ≤ r.val → Packing s target k) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with k > r and k >= 0, there do not exist pairwise disjoint sets I_1, ..., I_k of indices of s such that for every j with 1 <= j <= k, len(I_j) = len(target) and the multiset of bytes {s[i] | i in I_j} is equal to the multiset of bytes {target[i] | 0 <= i < len(target)}.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_12 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ k : Nat, r.val < (k : Int) → ¬ Packing s target k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ k : Nat, r.val < (k : Int) → ¬ Packing s target k) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122), and count(s,c) = count(target,c) for every byte c. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c. -/
theorem spec_13 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (h_counts : ∀ c : Std.U8, count s c = count target c)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    r.val = 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (h_counts : ∀ c : Std.U8, count s c = count target c)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, for every byte c with count(target,c) = 0 and every slice s' of bytes such that 1 <= len(s') <= 100, every byte of s' is an ASCII lowercase letter, len(s') = len(s) + 1, count(s',c) = count(s,c) + 1, and count(s',b) = count(s,b) for every byte b different from c, the call rearrange_characters(s', target) returns a result equal to r. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_14 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ c : Std.U8, count target c = 0 →
      ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
        s'.val.length = s.val.length + 1 →
        count s' c = count s c + 1 →
        (∀ b : Std.U8, b ≠ c → count s' b = count s b) →
        Aegis.RearrangeCharacters.rearrange_characters s' target = ok r := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ c : Std.U8, count target c = 0 →
      ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
        s'.val.length = s.val.length + 1 →
        count s' c = count s c + 1 →
        (∀ b : Std.U8, b ≠ c → count s' b = count s b) →
        Aegis.RearrangeCharacters.rearrange_characters s' target = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every slice s' of bytes such that 1 <= len(s') <= 100, every byte of s' is an ASCII lowercase letter, and count(s',c) = count(s,c) + count(target,c) for every byte c, the call rearrange_characters(s', target) returns a result r' with r' = r + 1. Here count(x,c) denotes the number of indices i with 0 <= i < len(x) and x[i] = c.
  Preconditions: s and target are slices of bytes, 1 <= len(s) <= 100, 1 <= len(target) <= 10, and every byte of s and of target is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_15 (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r) :
    ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
      (∀ c : Std.U8, count s' c = count s c + count target c) →
      ∃ r' : Std.I64,
        Aegis.RearrangeCharacters.rearrange_characters s' target = ok r' ∧ r'.val = r.val + 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s target : Slice Std.U8)
    (hs_len1 : 1 ≤ s.val.length) (hs_len100 : s.val.length ≤ 100)
    (ht_len1 : 1 ≤ target.val.length) (ht_len10 : target.val.length ≤ 10)
    (hs_lower : IsLower s) (ht_lower : IsLower target)
    (r : Std.I64) (h_r : Aegis.RearrangeCharacters.rearrange_characters s target = ok r), ∀ s' : Slice Std.U8, 1 ≤ s'.val.length → s'.val.length ≤ 100 → IsLower s' →
      (∀ c : Std.U8, count s' c = count s c + count target c) →
      ∃ r' : Std.I64,
        Aegis.RearrangeCharacters.rearrange_characters s' target = ok r' ∧ r'.val = r.val + 1) := by
  sorry

end AegisSpec.RearrangeCharacters
