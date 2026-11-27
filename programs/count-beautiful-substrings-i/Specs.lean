import Aegis.BeautifulSubstrings.Code.Funs

/-!
# Specifications of `Aegis.BeautifulSubstrings.beautiful_substrings`

LeetCode problem `count-beautiful-substrings-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.BeautifulSubstrings

namespace AegisSpec.BeautifulSubstrings

def isLowerAscii (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def isVowelByte (b : U8) : Bool :=
  b.val == 97 || b.val == 101 || b.val == 105 || b.val == 111 || b.val == 117

def vowelCount (l : List U8) (i j : ℕ) : ℕ :=
  ((l.drop i).take (j - i)).countP isVowelByte

def consonantCount (l : List U8) (i j : ℕ) : ℕ :=
  (j - i) - vowelCount l i j

def IsBeautifulPair (l : List U8) (k : ℤ) (i j : ℕ) : Prop :=
  i < j ∧ j ≤ l.length ∧ vowelCount l i j = consonantCount l i j ∧
    ((vowelCount l i j : ℤ) * (consonantCount l i j : ℤ)) % k = 0

instance (l : List U8) (k : ℤ) (i j : ℕ) : Decidable (IsBeautifulPair l k i j) := by
  unfold IsBeautifulPair
  infer_instance

def beautifulPairCount (l : List U8) (k : ℤ) : ℕ :=
  ((List.range (l.length + 1)).product (List.range (l.length + 1))).countP
    (fun q => decide (IsBeautifulPair l k q.1 q.2))

def HasBeautifulPair (l : List U8) (k : ℤ) : Prop := ∃ i j, IsBeautifulPair l k i j

theorem usizeMax_ge_1001 : 1001 ≤ Usize.max := by
  simp only [Aeneas.Std.Usize.max]
  rw [Aeneas.Std.Usize.numBits_eq]
  have h2 : 16 ≤ System.Platform.numBits := System.Platform.sixteen_le_numBits
  have h3 : 2 ^ 16 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by norm_num) h2
  norm_num at h3 ⊢
  omega

def reverseSlice (s : Slice U8) (h : s.val.length ≤ 1000) : Slice U8 :=
  Slice.from s.val.reverse (by
    have hmax := usizeMax_ge_1001
    simp only [List.length_reverse]
    omega)

def appendByte (s : Slice U8) (b : U8) (h : s.val.length ≤ 999) : Slice U8 :=
  Slice.from (s.val ++ [b]) (by
    have hmax := usizeMax_ge_1001
    simp only [List.length_append, List.length_singleton]
    omega)

theorem reverseSlice_val (s : Slice U8) (h : s.val.length ≤ 1000) :
    (reverseSlice s h).val = s.val.reverse :=
  Slice.from_val _ _

theorem appendByte_val (s : Slice U8) (b : U8) (h : s.val.length ≤ 999) :
    (appendByte s b h).val = s.val ++ [b] :=
  Slice.from_val _ _

/-- Let n = len(s). For 0 <= i < j <= n, let v(i,j) be the number of indices t with i <= t < j and s[t] in {'a','e','i','o','u'}, and let c(i,j) = (j-i) - v(i,j). The function returns a result r and r equals the number of pairs (i,j) with 0 <= i < j <= n such that v(i,j) = c(i,j) and (v(i,j) * c(i,j)) mod k = 0.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_1 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∃ r, beautiful_substrings s k = ok r ∧ r.val = ((beautifulPairCount s.val k.val : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∃ r, beautiful_substrings s k = ok r ∧ r.val = ((beautifulPairCount s.val k.val : ℕ) : ℤ)) := by
  sorry

/-- For every s and k satisfying the preconditions, the function returns a result r; it does not panic, overflow, or access out of bounds.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_2 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∃ r, beautiful_substrings s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∃ r, beautiful_substrings s k = ok r) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, 0 <= r <= n*(n+1)/2.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_3 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∀ r, beautiful_substrings s k = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∀ r, beautiful_substrings s k = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- The function returns 0.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000; either there is no index t with 0 <= t < len(s) and s[t] in {'a','e','i','o','u'}, or there is no index t with 0 <= t < len(s) and s[t] not in {'a','e','i','o','u'}. -/
theorem spec_4 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000)
    (h_edge : (∀ b ∈ s.val, isVowelByte b = false) ∨ (∀ b ∈ s.val, isVowelByte b = true)) :
    ∃ r, beautiful_substrings s k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000)
    (h_edge : (∀ b ∈ s.val, isVowelByte b = false) ∨ (∀ b ∈ s.val, isVowelByte b = true)), ∃ r, beautiful_substrings s k = ok r ∧ r.val = 0) := by
  sorry

/-- Let r1 be the result of beautiful_substrings(s, k1) and r2 be the result of beautiful_substrings(s, k2). Both calls return results, and r1 >= r2.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k1 <= 1000; 1 <= k2 <= 1000; k1 divides k2. -/
theorem spec_5 (s : Slice U8) (k1 k2 : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k1_lower : 1 ≤ k1.val) (h_k1_upper : k1.val ≤ 1000)
    (h_k2_lower : 1 ≤ k2.val) (h_k2_upper : k2.val ≤ 1000)
    (h_dvd : k1.val ∣ k2.val) :
    ∃ r1 r2, beautiful_substrings s k1 = ok r1 ∧ beautiful_substrings s k2 = ok r2 ∧
      r2.val ≤ r1.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (k1 k2 : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k1_lower : 1 ≤ k1.val) (h_k1_upper : k1.val ≤ 1000)
    (h_k2_lower : 1 ≤ k2.val) (h_k2_upper : k2.val ≤ 1000)
    (h_dvd : k1.val ∣ k2.val), ∃ r1 r2, beautiful_substrings s k1 = ok r1 ∧ beautiful_substrings s k2 = ok r2 ∧
      r2.val ≤ r1.val) := by
  sorry

/-- The calls beautiful_substrings(s1,k) and beautiful_substrings(s2,k) both return results r1 and r2, and r1 = r2.
  Preconditions: len(s1) = len(s2) <= 1000; every byte of s1 and s2 is an ASCII lowercase letter 'a'..'z'; for every i with 0 <= i < len(s1), s1[i] in {'a','e','i','o','u'} if and only if s2[i] in {'a','e','i','o','u'}; 1 <= k <= 1000. -/
theorem spec_6 (s1 s2 : Slice U8) (k : I64)
    (h_len : s1.val.length ≤ 1000)
    (h_len_eq : s1.val.length = s2.val.length)
    (h_lower1 : ∀ b ∈ s1.val, isLowerAscii b)
    (h_lower2 : ∀ b ∈ s2.val, isLowerAscii b)
    (h_pattern : ∀ (i : ℕ) (h1 : i < s1.val.length) (h2 : i < s2.val.length),
      isVowelByte (s1.val.get ⟨i, h1⟩) = isVowelByte (s2.val.get ⟨i, h2⟩))
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∃ r1 r2, beautiful_substrings s1 k = ok r1 ∧ beautiful_substrings s2 k = ok r2 ∧
      r1.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s1 s2 : Slice U8) (k : I64)
    (h_len : s1.val.length ≤ 1000)
    (h_len_eq : s1.val.length = s2.val.length)
    (h_lower1 : ∀ b ∈ s1.val, isLowerAscii b)
    (h_lower2 : ∀ b ∈ s2.val, isLowerAscii b)
    (h_pattern : ∀ (i : ℕ) (h1 : i < s1.val.length) (h2 : i < s2.val.length),
      isVowelByte (s1.val.get ⟨i, h1⟩) = isVowelByte (s2.val.get ⟨i, h2⟩))
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∃ r1 r2, beautiful_substrings s1 k = ok r1 ∧ beautiful_substrings s2 k = ok r2 ∧
      r1.val = r2.val) := by
  sorry

/-- Let n = len(s) and let rev(s) be the sequence of length n with rev(s)[i] = s[n-1-i] for every 0 <= i < n. The calls beautiful_substrings(s,k) and beautiful_substrings(rev(s),k) both return results r and r', and r = r'.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_7 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∃ r r', beautiful_substrings s k = ok r ∧
      beautiful_substrings (reverseSlice s h_len) k = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∃ r r', beautiful_substrings s k = ok r ∧
      beautiful_substrings (reverseSlice s h_len) k = ok r' ∧ r.val = r'.val) := by
  sorry

/-- Let n = len(s). For 0 <= i < j <= n, let v(i,j) be the number of indices t with i <= t < j and s[t] in {'a','e','i','o','u'}, and let c(i,j) = (j-i) - v(i,j). If the function returns r, then r = 0 if and only if there is no pair (i,j) with 0 <= i < j <= n such that v(i,j) = c(i,j) and (v(i,j)*c(i,j)) mod k = 0.
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_8 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∀ r, beautiful_substrings s k = ok r → (r.val = 0 ↔ ¬ HasBeautifulPair s.val k.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∀ r, beautiful_substrings s k = ok r → (r.val = 0 ↔ ¬ HasBeautifulPair s.val k.val)) := by
  sorry

/-- Let s' be the sequence of length len(s)+1 with s'[i] = s[i] for 0 <= i < len(s) and s'[len(s)] = ch. The calls beautiful_substrings(s,k) and beautiful_substrings(s',k) both return results r and r', and r <= r'.
  Preconditions: len(s) <= 999; every byte of s is an ASCII lowercase letter 'a'..'z'; ch is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_9 (s : Slice U8) (ch : U8) (k : I64)
    (h_len : s.val.length ≤ 999)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_ch : isLowerAscii ch)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∃ r r', beautiful_substrings s k = ok r ∧
      beautiful_substrings (appendByte s ch h_len) k = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (ch : U8) (k : I64)
    (h_len : s.val.length ≤ 999)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_ch : isLowerAscii ch)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∃ r r', beautiful_substrings s k = ok r ∧
      beautiful_substrings (appendByte s ch h_len) k = ok r' ∧ r.val ≤ r'.val) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, r <= floor(n*n/4).
  Preconditions: len(s) <= 1000; every byte of s is an ASCII lowercase letter 'a'..'z'; 1 <= k <= 1000. -/
theorem spec_10 (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000) :
    ∀ r, beautiful_substrings s k = ok r →
      r.val ≤ ((s.val.length * s.val.length / 4 : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (h_len : s.val.length ≤ 1000)
    (h_lower : ∀ b ∈ s.val, isLowerAscii b)
    (h_k_lower : 1 ≤ k.val) (h_k_upper : k.val ≤ 1000), ∀ r, beautiful_substrings s k = ok r →
      r.val ≤ ((s.val.length * s.val.length / 4 : ℕ) : ℤ)) := by
  sorry

end AegisSpec.BeautifulSubstrings
