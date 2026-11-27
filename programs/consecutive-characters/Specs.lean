import Aegis.MaxPower.Code.Funs

/-!
# Specifications of `Aegis.MaxPower.max_power`

LeetCode problem `consecutive-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxPower

def toListN {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
  | [] => .nil
  | a :: l => .cons a (toListN l)

theorem listN_toList_length {α : Type} {n : ℕ} (l : Aeneas.Data.ListN.ListN α n) :
    l.toList.length = n := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [Aeneas.Data.ListN.ListN.toList, ih]

theorem toListN_toList {α : Type} (l : List α) : (toListN l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [toListN, Aeneas.Data.ListN.ListN.toList, ih]

def byteAt (s : Slice U8) (i : ℕ) : ℕ :=
  ((s.val[i]?).map (fun b => b.val)).getD 0

def IsConstBlock (s : Slice U8) (l L : ℕ) : Prop :=
  ∀ j : ℕ, l ≤ j → j < l + L → byteAt s j = byteAt s l

def sliceOfList (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
  { leng := l.length, list := toListN l, bound := h }

theorem sliceOfList_val (l : List U8) (h : l.length ≤ Usize.max) :
    (sliceOfList l h).val = l := by
  simp [sliceOfList, Aeneas.Std.Slice.val, toListN_toList]

theorem val_length_le_max (s : Slice U8) : s.val.length ≤ Usize.max := by
  have h := s.bound
  have h' : s.val.length = s.leng := listN_toList_length s.list
  omega

def slicePrefix (s : Slice U8) (m : ℕ) : Slice U8 :=
  sliceOfList (s.val.take m) (by
    have hlen : (s.val.take m).length ≤ s.val.length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    have hbound : s.val.length ≤ Usize.max := val_length_le_max s
    omega)

def sliceMap (s : Slice U8) (g : U8 → U8) : Slice U8 :=
  sliceOfList (s.val.map g) (by
    have hlen : (s.val.map g).length = s.val.length := List.length_map ..
    have hbound : s.val.length ≤ Usize.max := val_length_le_max s
    omega)

theorem slicePrefix_val (s : Slice U8) (m : ℕ) :
    (slicePrefix s m).val = s.val.take m := by
  simp [slicePrefix, sliceOfList_val]

theorem sliceMap_val (s : Slice U8) (g : U8 → U8) :
    (sliceMap s g).val = s.val.map g := by
  simp [sliceMap, sliceOfList_val]

/-- Whenever the function returns a result r, the following hold. (a) r >= 1. (b) There exist integers l with 0 <= l and l + r <= len(s) such that s[j] = s[l] for every j with l <= j < l + r. (c) For every l and L with 0 <= l, 1 <= L, and l + L <= len(s), if s[j] = s[l] for every j with l <= j < l + L, then L <= r. Equivalently, r is the maximum length of a non-empty contiguous substring of s whose bytes are all equal.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_1 (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r) :
    1 ≤ r.val ∧
      (∃ l : ℕ, l + r.val.toNat ≤ s.val.length ∧ IsConstBlock s l r.val.toNat) ∧
      (∀ l L : ℕ, 1 ≤ L → l + L ≤ s.val.length → IsConstBlock s l L → (L : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r), 1 ≤ r.val ∧
      (∃ l : ℕ, l + r.val.toNat ≤ s.val.length ∧ IsConstBlock s l r.val.toNat) ∧
      (∀ l L : ℕ, 1 ≤ L → l + L ≤ s.val.length → IsConstBlock s l L → (L : ℤ) ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(s).
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r) :
    1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r), 1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index l such that 0 <= l, l + r <= len(s), s[j] = s[l] for every j with l <= j < l + r, and the block is maximal: either l = 0 or s[l-1] != s[l], and either l + r = len(s) or s[l+r] != s[l]. Thus r is the length of some maximal run of equal consecutive bytes.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r) :
    ∃ l : ℕ, l + r.val.toNat ≤ s.val.length ∧ IsConstBlock s l r.val.toNat ∧
      (l = 0 ∨ byteAt s (l - 1) ≠ byteAt s l) ∧
      (l + r.val.toNat = s.val.length ∨ byteAt s (l + r.val.toNat) ≠ byteAt s l) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r), ∃ l : ℕ, l + r.val.toNat ≤ s.val.length ∧ IsConstBlock s l r.val.toNat ∧
      (l = 0 ∨ byteAt s (l - 1) ≠ byteAt s l) ∧
      (l + r.val.toNat = s.val.length ∨ byteAt s (l + r.val.toNat) ≠ byteAt s l)) := by
  sorry

/-- Whenever the function returns a result r, for every l and L with 0 <= l, 1 <= L, and l + L <= len(s), if s[j] = s[l] for every j with l <= j < l + L, then L <= r. In other words, no constant contiguous substring of s is longer than r.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r) :
    ∀ l L : ℕ, 1 ≤ L → l + L ≤ s.val.length → IsConstBlock s l L → (L : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r), ∀ l L : ℕ, 1 ≤ L → l + L ≤ s.val.length → IsConstBlock s l L → (L : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if for every i with 0 <= i < len(s) - 1, s[i] != s[i+1].
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r) :
    r.val = 1 ↔ ∀ i : ℕ, i < s.val.length - 1 → byteAt s i ≠ byteAt s (i + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r), r.val = 1 ↔ ∀ i : ℕ, i < s.val.length - 1 → byteAt s i ≠ byteAt s (i + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 1 <= k <= r there exists an index l such that 0 <= l, l + k <= len(s), and s[j] = s[l] for every j with l <= j < l + k. Thus every length from 1 through r occurs as a constant contiguous substring.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r) :
    ∀ k : ℕ, 1 ≤ k → k ≤ r.val.toNat →
      ∃ l : ℕ, l + k ≤ s.val.length ∧ IsConstBlock s l k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (r : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : Aegis.MaxPower.max_power s = ok r), ∀ k : ℕ, 1 ≤ k → k ≤ r.val.toNat →
      ∃ l : ℕ, l + k ≤ s.val.length ∧ IsConstBlock s l k) := by
  sorry

/-- For every s with len(s) >= 2 and s[len(s)-2] != s[len(s)-1], if the function returns r on s and r' on the prefix slice s[0:len(s)-1], then r = r'.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice U8) (r r' : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hlen2 : 2 ≤ s.val.length)
    (hne : byteAt s (s.val.length - 2) ≠ byteAt s (s.val.length - 1))
    (hr : Aegis.MaxPower.max_power s = ok r)
    (hr' : Aegis.MaxPower.max_power (slicePrefix s (s.val.length - 1)) = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (r r' : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hlen2 : 2 ≤ s.val.length)
    (hne : byteAt s (s.val.length - 2) ≠ byteAt s (s.val.length - 1))
    (hr : Aegis.MaxPower.max_power s = ok r)
    (hr' : Aegis.MaxPower.max_power (slicePrefix s (s.val.length - 1)) = ok r'), r = r') := by
  sorry

/-- For every slice t satisfying 1 <= len(t) <= 500 and 97 <= t[i] <= 122 for all i with 0 <= i < len(t), if len(t) = len(s) and t[i] = s[len(s)-1-i] for every i with 0 <= i < len(s), and if the function returns r on s and r' on t, then r = r'.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_8 (s t : Slice U8) (r r' : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (htlen : 1 ≤ t.val.length) (htlen' : t.val.length ≤ 500)
    (htbytes : ∀ i : ℕ, i < t.val.length → 97 ≤ byteAt t i ∧ byteAt t i ≤ 122)
    (hrevlen : t.val.length = s.val.length)
    (hrev : ∀ i : ℕ, i < s.val.length → byteAt t i = byteAt s (s.val.length - 1 - i))
    (hr : Aegis.MaxPower.max_power s = ok r)
    (hr' : Aegis.MaxPower.max_power t = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8) (r r' : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (htlen : 1 ≤ t.val.length) (htlen' : t.val.length ≤ 500)
    (htbytes : ∀ i : ℕ, i < t.val.length → 97 ≤ byteAt t i ∧ byteAt t i ≤ 122)
    (hrevlen : t.val.length = s.val.length)
    (hrev : ∀ i : ℕ, i < s.val.length → byteAt t i = byteAt s (s.val.length - 1 - i))
    (hr : Aegis.MaxPower.max_power s = ok r)
    (hr' : Aegis.MaxPower.max_power t = ok r'), r = r') := by
  sorry

/-- For every bijection f from the set {97,98,...,122} to itself, let t be the slice with len(t) = len(s) and t[i] = f(s[i]) for every i with 0 <= i < len(s). If the function returns r on s and r' on t, then r = r'.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice U8) (f : U8 → U8) (r r' : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hf_maps : ∀ b : U8, 97 ≤ b.val → b.val ≤ 122 → 97 ≤ (f b).val ∧ (f b).val ≤ 122)
    (hf_inj : ∀ b₁ b₂ : U8, 97 ≤ b₁.val → b₁.val ≤ 122 → 97 ≤ b₂.val → b₂.val ≤ 122 →
      f b₁ = f b₂ → b₁ = b₂)
    (hr : Aegis.MaxPower.max_power s = ok r)
    (hr' : Aegis.MaxPower.max_power (sliceMap s f) = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (f : U8 → U8) (r r' : I64)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hf_maps : ∀ b : U8, 97 ≤ b.val → b.val ≤ 122 → 97 ≤ (f b).val ∧ (f b).val ≤ 122)
    (hf_inj : ∀ b₁ b₂ : U8, 97 ≤ b₁.val → b₁.val ≤ 122 → 97 ≤ b₂.val → b₂.val ≤ 122 →
      f b₁ = f b₂ → b₁ = b₂)
    (hr : Aegis.MaxPower.max_power s = ok r)
    (hr' : Aegis.MaxPower.max_power (sliceMap s f) = ok r'), r = r') := by
  sorry

/-- The function returns a result for every input satisfying the preconditions; it does not fail due to overflow, out-of-bounds indexing, or panic.
  Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r : I64, Aegis.MaxPower.max_power s = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 500)
    (hbytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : I64, Aegis.MaxPower.max_power s = ok r) := by
  sorry

end AegisSpec.MaxPower
