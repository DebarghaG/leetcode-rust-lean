import Aegis.MaxSubstringLength.Code.Funs

/-!
# Specifications of `Aegis.MaxSubstringLength.max_substring_length`

LeetCode problem `select-k-disjoint-special-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSubstringLength

namespace AegisSpec.MaxSubstringLength

def byteVal (s : Slice Std.U8) (i : ℕ) : ℕ :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def OccursIn (s : Slice Std.U8) (l r c : ℕ) : Prop :=
  ∃ i, l ≤ i ∧ i ≤ r ∧ i < s.val.length ∧ byteVal s i = c

def IsSpecial (s : Slice Std.U8) (l r : ℕ) : Prop :=
  l ≤ r ∧
    r < s.val.length ∧
    ¬ (l = 0 ∧ r = s.val.length - 1) ∧
    ∀ i j, l ≤ i → i ≤ r → j < s.val.length → (j < l ∨ r < j) →
      byteVal s j ≠ byteVal s i

def SpecialChain (s : Slice Std.U8) (m : ℕ) (l r : ℕ → ℕ) : Prop :=
  (∀ t, t < m → IsSpecial s (l t) (r t)) ∧
    (∀ t, t + 1 < m → r t < l (t + 1))

def distinctByteCount (s : Slice Std.U8) : ℕ :=
  (s.val.map (fun b => b.val)).dedup.length

noncomputable def uniqueIndexSet (s : Slice Std.U8) : Finset ℕ :=
  (Finset.range s.val.length).filter
    (fun i => ∀ j, j < s.val.length → j ≠ i → byteVal s j ≠ byteVal s i)

/-- Let n = len(s). For integers l,r with 0 <= l <= r < n, call the interval [l,r] special if (1) it is not the whole string, i.e. not (l = 0 and r = n-1), and (2) for every i with l <= i <= r and every j with 0 <= j < n and (j < l or j > r), s[j] != s[i]. Then max_substring_length(s,k) returns a Boolean result b, and b = true if and only if there exist k pairwise disjoint special intervals. More explicitly, b = true iff either k = 0, or there are integers l_1,...,l_k and r_1,...,r_k with 0 <= l_1 <= r_1 < l_2 <= r_2 < ... < l_k <= r_k < n such that every [l_t,r_t] is special. Pairwise disjoint means no index i belongs to two selected intervals.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_1 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122) :
    ∃ b : Bool, max_substring_length s k = ok b ∧
      (b = true ↔
        k.val = 0 ∨ ∃ l r : ℕ → ℕ, SpecialChain s k.val.toNat l r) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122), ∃ b : Bool, max_substring_length s k = ok b ∧
      (b = true ↔
        k.val = 0 ∨ ∃ l r : ℕ → ℕ, SpecialChain s k.val.toNat l r)) := by
  sorry

/-- Under the preconditions, the call max_substring_length(s,k) returns some Boolean result (it does not fail, panic, overflow, or access an index out of bounds).
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_2 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122) :
    ∃ r : Bool, max_substring_length s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122), ∃ r : Bool, max_substring_length s k = ok r) := by
  sorry

/-- Let d be the number of distinct byte values among s[0],...,s[n-1]. If k > d, then max_substring_length(s,k) returns false.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_3 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122) :
    k.val > (distinctByteCount s : ℤ) →
      max_substring_length s k = ok false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122), k.val > (distinctByteCount s : ℤ) →
      max_substring_length s k = ok false) := by
  sorry

/-- If all bytes of s are equal (s[0] = s[1] = ... = s[n-1]), then max_substring_length(s,k) returns true if and only if k = 0.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_4 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hall : ∀ i j, i < n → j < n → byteVal s i = byteVal s j) :
    max_substring_length s k = ok true ↔ k.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hall : ∀ i j, i < n → j < n → byteVal s i = byteVal s j), max_substring_length s k = ok true ↔ k.val = 0) := by
  sorry

/-- Let U = { i | 0 <= i < n and for every j with 0 <= j < n and j != i, s[j] != s[i] }. If k <= |U|, then max_substring_length(s,k) returns true.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_5 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hkU : k.val ≤ ((uniqueIndexSet s).card : ℤ)) :
    max_substring_length s k = ok true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hkU : k.val ≤ ((uniqueIndexSet s).card : ℤ)), max_substring_length s k = ok true) := by
  sorry

/-- Suppose there exist an integer m >= 2, indices 0 = p_0 < p_1 < ... < p_m = n, and pairwise distinct bytes c_1,...,c_m such that for every t with 1 <= t <= m and every i with p_{t-1} <= i < p_t, s[i] = c_t. Then max_substring_length(s,k) returns true if and only if k <= m.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_6 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (m : ℕ) (hm : 2 ≤ m) (p c : ℕ → ℕ)
    (hp0 : p 0 = 0) (hpm : p m = n)
    (hpmono : ∀ t, t < m → p t < p (t + 1))
    (hc : ∀ t, t < m → ∀ i, p t ≤ i → i < p (t + 1) → byteVal s i = c t)
    (hcne : ∀ t u, t < m → u < m → c t = c u → t = u) :
    max_substring_length s k = ok true ↔ k.val ≤ (m : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (m : ℕ) (hm : 2 ≤ m) (p c : ℕ → ℕ)
    (hp0 : p 0 = 0) (hpm : p m = n)
    (hpmono : ∀ t, t < m → p t < p (t + 1))
    (hc : ∀ t, t < m → ∀ i, p t ≤ i → i < p (t + 1) → byteVal s i = c t)
    (hcne : ∀ t u, t < m → u < m → c t = c u → t = u), max_substring_length s k = ok true ↔ k.val ≤ (m : ℤ)) := by
  sorry

/-- For every integer j with 0 <= j <= k, if max_substring_length(s,k) returns true, then max_substring_length(s,j) returns true.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_7 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122) :
    ∀ j : Std.I64, 0 ≤ j.val → j.val ≤ k.val →
      max_substring_length s k = ok true →
        max_substring_length s j = ok true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122), ∀ j : Std.I64, 0 ≤ j.val → j.val ≤ k.val →
      max_substring_length s k = ok true →
        max_substring_length s j = ok true) := by
  sorry

/-- Let rev be the byte array of length n with rev[i] = s[n-1-i] for every i with 0 <= i < n. Then max_substring_length(s,k) and max_substring_length(rev,k) return the same Boolean value.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_8 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (rev : Slice Std.U8) (hrevlen : rev.val.length = n)
    (hrev : ∀ i, i < n → byteVal rev i = byteVal s (n - 1 - i)) :
    ∀ b : Bool, max_substring_length s k = ok b ↔
      max_substring_length rev k = ok b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (rev : Slice Std.U8) (hrevlen : rev.val.length = n)
    (hrev : ∀ i, i < n → byteVal rev i = byteVal s (n - 1 - i)), ∀ b : Bool, max_substring_length s k = ok b ↔
      max_substring_length rev k = ok b) := by
  sorry

/-- For every permutation f of the set {97,98,...,122}, let s_f be the byte array with s_f[i] = f(s[i]) for every i with 0 <= i < n. Then max_substring_length(s,k) and max_substring_length(s_f,k) return the same Boolean value.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_9 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (f : ℕ → ℕ)
    (hf_maps : ∀ c, 97 ≤ c → c ≤ 122 → 97 ≤ f c ∧ f c ≤ 122)
    (hf_inj : ∀ c d, 97 ≤ c → c ≤ 122 → 97 ≤ d → d ≤ 122 →
      f c = f d → c = d)
    (sf : Slice Std.U8) (hsf_len : sf.val.length = n)
    (hsf : ∀ i, i < n → byteVal sf i = f (byteVal s i)) :
    ∀ b : Bool, max_substring_length s k = ok b ↔
      max_substring_length sf k = ok b := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (f : ℕ → ℕ)
    (hf_maps : ∀ c, 97 ≤ c → c ≤ 122 → 97 ≤ f c ∧ f c ≤ 122)
    (hf_inj : ∀ c d, 97 ≤ c → c ≤ 122 → 97 ≤ d → d ≤ 122 →
      f c = f d → c = d)
    (sf : Slice Std.U8) (hsf_len : sf.val.length = n)
    (hsf : ∀ i, i < n → byteVal sf i = f (byteVal s i)), ∀ b : Bool, max_substring_length s k = ok b ↔
      max_substring_length sf k = ok b) := by
  sorry

/-- Whenever max_substring_length(s,k) returns true and k > 0, there exist integers l_1,...,l_k and r_1,...,r_k with 0 <= l_1 <= r_1 < l_2 <= r_2 < ... < l_k <= r_k < n such that each [l_t,r_t] is special, and for any two distinct t,u, no byte value occurs at an index in [l_t,r_t] and also at an index in [l_u,r_u].
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_10 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122) :
    max_substring_length s k = ok true → 0 < k.val →
      ∃ l r : ℕ → ℕ, SpecialChain s k.val.toNat l r ∧
        ∀ t u, t < k.val.toNat → u < k.val.toNat → t ≠ u →
          ∀ c, ¬ (OccursIn s (l t) (r t) c ∧ OccursIn s (l u) (r u) c) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122), max_substring_length s k = ok true → 0 < k.val →
      ∃ l r : ℕ → ℕ, SpecialChain s k.val.toNat l r ∧
        ∀ t u, t < k.val.toNat → u < k.val.toNat → t ≠ u →
          ∀ c, ¬ (OccursIn s (l t) (r t) c ∧ OccursIn s (l u) (r u) c)) := by
  sorry

/-- Suppose n >= 4 and there exist distinct bytes a,b such that for every i with 0 <= i < n, s[i] = a when i is even and s[i] = b when i is odd, or s[i] = b when i is even and s[i] = a when i is odd. Then for every k with 1 <= k <= 26, max_substring_length(s,k) returns false.
  Preconditions: n = len(s); 2 <= n <= 50000; 0 <= k <= 26; and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s is a byte array of lowercase ASCII letters). -/
theorem spec_11 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hn4 : 4 ≤ n)
    (hab : ∃ a b : ℕ, a ≤ 255 ∧ b ≤ 255 ∧ a ≠ b ∧
      ((∀ i, i < n → byteVal s i = if i % 2 = 0 then a else b) ∨
       (∀ i, i < n → byteVal s i = if i % 2 = 0 then b else a)))
    (hk1 : 1 ≤ k.val) :
    max_substring_length s k = ok false := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hn4 : 4 ≤ n)
    (hab : ∃ a b : ℕ, a ≤ 255 ∧ b ≤ 255 ∧ a ≠ b ∧
      ((∀ i, i < n → byteVal s i = if i % 2 = 0 then a else b) ∨
       (∀ i, i < n → byteVal s i = if i % 2 = 0 then b else a)))
    (hk1 : 1 ≤ k.val), max_substring_length s k = ok false) := by
  sorry

/-- Under these preconditions, max_substring_length(s,k) returns false.
  Preconditions: n = len(s); 2 <= n <= 50000; 1 <= k <= 26; for every i with 0 <= i < n, 97 <= s[i] <= 122; and there exist integers m,p with m >= 2, p >= 2, n = m*p, the bytes s[0],...,s[m-1] are pairwise distinct, and s[i] = s[i mod m] for every i with 0 <= i < n. -/
theorem spec_12 (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hk1 : 1 ≤ k.val)
    (m p : ℕ) (hm : 2 ≤ m) (hp : 2 ≤ p) (hnmp : n = m * p)
    (hdistinct : ∀ i j, i < m → j < m → byteVal s i = byteVal s j → i = j)
    (hperiod : ∀ i, i < n → byteVal s i = byteVal s (i % m)) :
    max_substring_length s k = ok false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (n : ℕ)
    (hn : n = s.val.length) (hn2 : 2 ≤ n) (hn50000 : n ≤ 50000)
    (hk0 : 0 ≤ k.val) (hk26 : k.val ≤ 26)
    (hlower : ∀ i, i < n → 97 ≤ byteVal s i ∧ byteVal s i ≤ 122)
    (hk1 : 1 ≤ k.val)
    (m p : ℕ) (hm : 2 ≤ m) (hp : 2 ≤ p) (hnmp : n = m * p)
    (hdistinct : ∀ i j, i < m → j < m → byteVal s i = byteVal s j → i = j)
    (hperiod : ∀ i, i < n → byteVal s i = byteVal s (i % m)), max_substring_length s k = ok false) := by
  sorry

end AegisSpec.MaxSubstringLength
