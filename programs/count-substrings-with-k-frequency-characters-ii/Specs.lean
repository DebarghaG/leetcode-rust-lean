import Aegis.NumberOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubstrings.number_of_substrings`

LeetCode problem `count-substrings-with-k-frequency-characters-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.NumberOfSubstrings

open Aeneas Aeneas.Std Result Classical

open Aegis.NumberOfSubstrings

def occIn (s : List U8) (lo hi : ℕ) (c : U8) : ℕ :=
  ((s.drop lo).take (hi - lo)).countP (fun x => decide (x = c))

def hasFrequentByte (s : List U8) (lo hi : ℕ) (k : ℤ) : Prop :=
  ∃ c : U8, k ≤ (occIn s lo hi c : ℤ)

noncomputable def validPairCount (s : List U8) (k : ℤ) : ℕ :=
  ((List.range (s.length + 1)).map (fun l =>
    ((List.range (s.length + 1)).map (fun u =>
      if l < u ∧ u ≤ s.length ∧ hasFrequentByte s l u k then 1 else 0)).sum)).sum

def allEq (s : List U8) : Prop :=
  ∀ a, a ∈ s → ∀ b, b ∈ s → a = b

/-- Let r be the result returned by number_of_substrings(s, k). For integers l and u, call the half-open interval [l, u) valid if 0 <= l < u <= n and there exists a byte value c such that the number of indices i with l <= i < u and s[i] = c is at least k. Then r equals the number of valid pairs (l, u).
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_1 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val = (validPairCount s.val k.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val = (validPairCount s.val k.val : ℤ)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_2 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). Then 0 <= r <= n*(n+1)/2.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_3 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) * ((s.val.length : ℤ) + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) * ((s.val.length : ℤ) + 1) / 2) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). Then r <= (n-k+1)*(n-k+2)/2.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_4 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val ≤ ((s.val.length : ℤ) - k.val + 1) * ((s.val.length : ℤ) - k.val + 2) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val ≤ ((s.val.length : ℤ) - k.val + 1) * ((s.val.length : ℤ) - k.val + 2) / 2) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). Then r = n*(n+1)/2.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, k = 1, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_5 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk : k.val = 1)
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val = (s.val.length : ℤ) * ((s.val.length : ℤ) + 1) / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk : k.val = 1)
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val = (s.val.length : ℤ) * ((s.val.length : ℤ) + 1) / 2) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). Then r = 1 if all bytes of s are equal, and r = 0 otherwise.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, k = n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_6 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk : k.val = (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      (allEq s.val → r.val = 1) ∧ (¬ allEq s.val → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk : k.val = (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      (allEq s.val → r.val = 1) ∧ (¬ allEq s.val → r.val = 0)) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). Then r = (n-k+1)*(n-k+2)/2.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122), and all bytes of s are equal: s[0] = s[1] = ... = s[n-1]. -/
theorem spec_7 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (hall : allEq s.val) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val = ((s.val.length : ℤ) - k.val + 1) * ((s.val.length : ℤ) - k.val + 2) / 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (hall : allEq s.val), ∃ r : I64, number_of_substrings s k = ok r ∧
      r.val = ((s.val.length : ℤ) - k.val + 1) * ((s.val.length : ℤ) - k.val + 2) / 2) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). Then r > 0 if and only if there exists a byte value c whose total number of occurrences in all of s is at least k, i.e. the number of indices i with 0 <= i < n and s[i] = c is at least k.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_8 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      (0 < r.val ↔ hasFrequentByte s.val 0 s.val.length k.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      (0 < r.val ↔ hasFrequentByte s.val 0 s.val.length k.val)) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). For every integer k' with k <= k' <= n, the result returned by number_of_substrings(s, k') is at most r.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_9 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      ∀ k' : I64, k.val ≤ k'.val → k'.val ≤ (s.val.length : ℤ) →
        ∃ r' : I64, number_of_substrings s k' = ok r' ∧ r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      ∀ k' : I64, k.val ≤ k'.val → k'.val ≤ (s.val.length : ℤ) →
        ∃ r' : I64, number_of_substrings s k' = ok r' ∧ r'.val ≤ r.val) := by
  sorry

/-- Let reverse(s) be the slice t with len(t) = n and t[i] = s[n-1-i] for every 0 <= i < n. Then number_of_substrings(s, k) = number_of_substrings(reverse(s), k).
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_10 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (t : Slice U8) (ht : t.val = s.val.reverse) :
    number_of_substrings s k = number_of_substrings t k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (t : Slice U8) (ht : t.val = s.val.reverse), number_of_substrings s k = number_of_substrings t k) := by
  sorry

/-- Let f be a bijection from the set of lowercase ASCII letters to itself, and let t be the slice with len(t) = n and t[i] = f(s[i]) for every 0 <= i < n. Then number_of_substrings(s, k) = number_of_substrings(t, k).
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_11 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (f : U8 → U8)
    (hf_lower : ∀ c : U8, 97 ≤ c.val → c.val ≤ 122 → 97 ≤ (f c).val ∧ (f c).val ≤ 122)
    (hf_inj : ∀ a b : U8, 97 ≤ a.val → a.val ≤ 122 → 97 ≤ b.val → b.val ≤ 122 →
      f a = f b → a = b)
    (hf_surj : ∀ c : U8, 97 ≤ c.val → c.val ≤ 122 →
      ∃ a : U8, 97 ≤ a.val ∧ a.val ≤ 122 ∧ f a = c)
    (t : Slice U8) (ht : t.val = s.val.map f) :
    number_of_substrings s k = number_of_substrings t k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (f : U8 → U8)
    (hf_lower : ∀ c : U8, 97 ≤ c.val → c.val ≤ 122 → 97 ≤ (f c).val ∧ (f c).val ≤ 122)
    (hf_inj : ∀ a b : U8, 97 ≤ a.val → a.val ≤ 122 → 97 ≤ b.val → b.val ≤ 122 →
      f a = f b → a = b)
    (hf_surj : ∀ c : U8, 97 ≤ c.val → c.val ≤ 122 →
      ∃ a : U8, 97 ≤ a.val ∧ a.val ≤ 122 ∧ f a = c)
    (t : Slice U8) (ht : t.val = s.val.map f), number_of_substrings s k = number_of_substrings t k) := by
  sorry

/-- The result returned by number_of_substrings(s, k) is at least the result returned by number_of_substrings(t, k).
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). Also let t be a prefix of s: 0 <= len(t) <= n, t[i] = s[i] for every 0 <= i < len(t), and 1 <= k <= len(t). -/
theorem spec_12 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (t : Slice U8) (ht : ∃ m : ℕ, t.val = s.val.take m)
    (hkt : k.val ≤ (t.val.length : ℤ)) :
    ∃ rs rt : I64, number_of_substrings s k = ok rs ∧
      number_of_substrings t k = ok rt ∧ rt.val ≤ rs.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122)
    (t : Slice U8) (ht : ∃ m : ℕ, t.val = s.val.take m)
    (hkt : k.val ≤ (t.val.length : ℤ)), ∃ rs rt : I64, number_of_substrings s k = ok rs ∧
      number_of_substrings t k = ok rt ∧ rt.val ≤ rs.val) := by
  sorry

/-- Let r be the result returned by number_of_substrings(s, k). For every byte value c, if c occurs f times in s (that is, f is the number of indices i with 0 <= i < n and s[i] = c) and f >= k, then r >= f - k + 1.
  Preconditions: Let n = len(s). Assume 1 <= n <= 300000, 1 <= k <= n, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_13 (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : I64, number_of_substrings s k = ok r ∧
      ∀ (c : U8) (f : ℕ), f = occIn s.val 0 s.val.length c → k.val ≤ (f : ℤ) →
        (f : ℤ) - k.val + 1 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 300000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (s.val.length : ℤ))
    (hlower : ∀ c, c ∈ s.val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : I64, number_of_substrings s k = ok r ∧
      ∀ (c : U8) (f : ℕ), f = occIn s.val 0 s.val.length c → k.val ≤ (f : ℤ) →
        (f : ℤ) - k.val + 1 ≤ r.val) := by
  sorry

end AegisSpec.NumberOfSubstrings
