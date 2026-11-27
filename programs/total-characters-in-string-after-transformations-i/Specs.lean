import Aegis.LengthAfterTransformations.Code.Funs

/-!
# Specifications of `Aegis.LengthAfterTransformations.length_after_transformations`

LeetCode problem `total-characters-in-string-after-transformations-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LengthAfterTransformations

  namespace AegisSpec.LengthAfterTransformations

  def MOD : ℤ := 1000000007

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def stepByte (c : ℕ) : List ℕ := if c = 122 then [97, 98] else [c + 1]

  def F (l : List ℕ) : List ℕ := l.flatMap stepByte

  def Fiter : ℕ → List ℕ → List ℕ
    | 0, l => l
    | k + 1, l => F (Fiter k l)

  def count (l : List ℕ) (c : ℕ) : ℕ := (l.filter (fun x => x = c)).length

  def zCount (l : List ℕ) : ℕ := count l 122

  def zPartialSum : ℕ → List ℕ → ℕ
    | 0, _ => 0
    | k + 1, l => zCount l + zPartialSum k (F l)

  def L (t c : ℕ) : ℕ := (Fiter t [c]).length

  def shapeSum (t : ℕ) (l : List ℕ) : ℕ :=
    ((List.range 26).map (fun i => count l (97 + i) * L t (97 + i))).sum

  def i64Succ (t : Std.I64) : Std.I64 := ⟨t.bv + (1 : BitVec 64)⟩

  def i64Pred (t : Std.I64) : Std.I64 := ⟨t.bv - (1 : BitVec 64)⟩

  def IsLowercase (s : Slice Std.U8) : Prop :=
    ∀ (i : ℕ) (hi : i < s.val.length),
      97 ≤ (s.val.get ⟨i, hi⟩).val ∧ (s.val.get ⟨i, hi⟩).val ≤ 122

  /-- Let `M = 1000000007`. Let `F` be the map on byte strings that replaces each byte by the string consisting of its successor (`'a'` to `'b'`, ..., `'y'` to `'z'`) and replaces `'z'` by the two-byte string `ab`, then concatenates the replacements in the original order; let `F^k` denote k-fold iteration with `F^0(x)=x`. Whenever the function returns a result `r`, `r` is the unique integer satisfying `0 <= r < M` and `r ≡ len(F^t(s)) (mod M)`; equivalently `r = len(F^t(s)) mod M`.
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; for every `i` with `0 <= i < len(s)`, the byte `s[i]` satisfies `97 <= s[i] <= 122` (lowercase ASCII); and `1 <= t <= 100000`, with `t` viewed as a natural number in exponents. -/
  theorem spec_1 (s : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000) :
      ∀ r : Std.I64,
        length_after_transformations s t = ok r →
        r.val = ((Fiter t.val.toNat (bytes s)).length : ℤ) % MOD := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000), ∀ r : Std.I64,
          length_after_transformations s t = ok r →
          r.val = ((Fiter t.val.toNat (bytes s)).length : ℤ) % MOD) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result `r` of type `i64` (it does not fail or panic).
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; for every `i` with `0 <= i < len(s)`, `97 <= s[i] <= 122`; and `1 <= t <= 100000`. -/
  theorem spec_2 (s : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000) :
      ∃ r : Std.I64, length_after_transformations s t = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000), ∃ r : Std.I64, length_after_transformations s t = ok r) := by
    sorry

  /-- Let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. For every input satisfying the preconditions with `t <= 25`, whenever the function returns `r`, `r = len(s) + N`, where `N` is the number of indices `i` with `0 <= i < len(s)` and `s[i] + t > 122`.
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; for every `i` with `0 <= i < len(s)`, `97 <= s[i] <= 122`; and `1 <= t <= 25`. -/
  theorem spec_3 (s : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 25) :
      ∀ r : Std.I64,
        length_after_transformations s t = ok r →
        r.val = (s.val.length : ℤ) +
          ((s.val.filter (fun b => 122 < (b.val : ℤ) + t.val)).length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 25), ∀ r : Std.I64,
          length_after_transformations s t = ok r →
          r.val = (s.val.length : ℤ) +
            ((s.val.filter (fun b => 122 < (b.val : ℤ) + t.val)).length : ℤ)) := by
    sorry

  /-- Let `M = 1000000007` and let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. For each byte `c`, let `L_t(c) = len(F^t([c]))`, the length after `t` transformations of the one-character string `[c]`. Whenever the function returns `r`, `r ≡ sum_{c=97}^{122} count_s(c) * L_t(c) (mod M)`, where `count_s(c)` is the number of indices `i` with `0 <= i < len(s)` and `s[i] = c`.
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; for every `i` with `0 <= i < len(s)`, `97 <= s[i] <= 122`; and `1 <= t <= 100000`. -/
  theorem spec_4 (s : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000) :
      ∀ r : Std.I64,
        length_after_transformations s t = ok r →
        r.val % MOD = ((shapeSum t.val.toNat (bytes s) : ℕ) : ℤ) % MOD := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000), ∀ r : Std.I64,
          length_after_transformations s t = ok r →
          r.val % MOD = ((shapeSum t.val.toNat (bytes s) : ℕ) : ℤ) % MOD) := by
    sorry

  /-- Let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. If for every byte `c` with `97 <= c <= 122`, the number of occurrences of `c` in `s1` equals the number of occurrences of `c` in `s2`, then whenever the function returns `r1` on `(s1,t)` and `r2` on `(s2,t)`, `r1 = r2`.
    Preconditions: `len(s1) >= 1`, `len(s1) <= 100000`, `len(s2) >= 1`, `len(s2) <= 100000`; all bytes of `s1` and `s2` are in `97..122`; and `1 <= t <= 100000`. -/
  theorem spec_5 (s1 s2 : Slice Std.U8) (t : Std.I64)
      (h_len1_ge : 1 ≤ s1.val.length) (h_len1_le : s1.val.length ≤ 100000)
      (h_len2_ge : 1 ≤ s2.val.length) (h_len2_le : s2.val.length ≤ 100000)
      (h_lower1 : IsLowercase s1) (h_lower2 : IsLowercase s2)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000)
      (h_counts : ∀ c : ℕ, 97 ≤ c → c ≤ 122 → count (bytes s1) c = count (bytes s2) c) :
      ∀ r1 r2 : Std.I64,
        length_after_transformations s1 t = ok r1 →
        length_after_transformations s2 t = ok r2 →
        r1.val = r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8) (t : Std.I64)
        (h_len1_ge : 1 ≤ s1.val.length) (h_len1_le : s1.val.length ≤ 100000)
        (h_len2_ge : 1 ≤ s2.val.length) (h_len2_le : s2.val.length ≤ 100000)
        (h_lower1 : IsLowercase s1) (h_lower2 : IsLowercase s2)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000)
        (h_counts : ∀ c : ℕ, 97 ≤ c → c ≤ 122 → count (bytes s1) c = count (bytes s2) c), ∀ r1 r2 : Std.I64,
          length_after_transformations s1 t = ok r1 →
          length_after_transformations s2 t = ok r2 →
          r1.val = r2.val) := by
    sorry

  /-- Let `M = 1000000007` and let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. Let `s1 ++ s2` be the concatenation of the two byte strings. Whenever the function returns `r` on `(s1 ++ s2, t)`, `r1` on `(s1,t)`, and `r2` on `(s2,t)`, we have `r ≡ r1 + r2 (mod M)`.
    Preconditions: `len(s1) >= 1`, `len(s2) >= 1`, `len(s1) + len(s2) <= 100000`; all bytes of `s1` and `s2` are in `97..122`; and `1 <= t <= 100000`. -/
  theorem spec_6 (s1 s2 s : Slice Std.U8) (t : Std.I64)
      (h_len1_ge : 1 ≤ s1.val.length)
      (h_len2_ge : 1 ≤ s2.val.length)
      (h_len_sum : s1.val.length + s2.val.length ≤ 100000)
      (h_lower1 : IsLowercase s1) (h_lower2 : IsLowercase s2)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000)
      (h_cat : s.val = s1.val ++ s2.val) :
      ∀ r r1 r2 : Std.I64,
        length_after_transformations s t = ok r →
        length_after_transformations s1 t = ok r1 →
        length_after_transformations s2 t = ok r2 →
        r.val % MOD = (r1.val + r2.val) % MOD := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s1 s2 s : Slice Std.U8) (t : Std.I64)
        (h_len1_ge : 1 ≤ s1.val.length)
        (h_len2_ge : 1 ≤ s2.val.length)
        (h_len_sum : s1.val.length + s2.val.length ≤ 100000)
        (h_lower1 : IsLowercase s1) (h_lower2 : IsLowercase s2)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000)
        (h_cat : s.val = s1.val ++ s2.val), ∀ r r1 r2 : Std.I64,
          length_after_transformations s t = ok r →
          length_after_transformations s1 t = ok r1 →
          length_after_transformations s2 t = ok r2 →
          r.val % MOD = (r1.val + r2.val) % MOD) := by
    sorry

  /-- Let `M = 1000000007` and let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. For `k >= 0`, let `Z_k(s)` be the number of `'z'` bytes in `F^k(s)`. Whenever the function returns `r_t` on `(s,t)` and `r_{t+1}` on `(s,t+1)`, `r_{t+1} ≡ r_t + Z_t(s) (mod M)`.
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; all bytes of `s` are in `97..122`; and `1 <= t <= 99999`. -/
  theorem spec_7 (s : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 99999) :
      ∀ r r' : Std.I64,
        length_after_transformations s t = ok r →
        length_after_transformations s (i64Succ t) = ok r' →
        r'.val % MOD = (r.val + (zCount (Fiter t.val.toNat (bytes s)) : ℤ)) % MOD := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 99999), ∀ r r' : Std.I64,
          length_after_transformations s t = ok r →
          length_after_transformations s (i64Succ t) = ok r' →
          r'.val % MOD = (r.val + (zCount (Fiter t.val.toNat (bytes s)) : ℤ)) % MOD) := by
    sorry

  /-- Let `M = 1000000007` and let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. For `k >= 0`, let `Z_k(s)` be the number of `'z'` bytes in `F^k(s)`. Whenever the function returns `r`, `r ≡ len(s) + sum_{k=0}^{t-1} Z_k(s) (mod M)`.
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; all bytes of `s` are in `97..122`; and `1 <= t <= 100000`. -/
  theorem spec_8 (s : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000) :
      ∀ r : Std.I64,
        length_after_transformations s t = ok r →
        r.val % MOD =
          ((s.val.length : ℤ) + (zPartialSum t.val.toNat (bytes s) : ℤ)) % MOD := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 1 ≤ t.val) (h_t_le : t.val ≤ 100000), ∀ r : Std.I64,
          length_after_transformations s t = ok r →
          r.val % MOD =
            ((s.val.length : ℤ) + (zPartialSum t.val.toNat (bytes s) : ℤ)) % MOD) := by
    sorry

  /-- Let `F` be the one-step transformation on strings that sends `'z'` to `ab` and every other lowercase letter to its successor, applied characterwise and concatenated. Whenever the function returns `r` on `(s,t)` and `r'` on `(F(s), t-1)`, `r = r'`.
    Preconditions: `len(s) >= 1` and `len(s) <= 100000`; all bytes of `s` are in `97..122`; `2 <= t <= 100000`; and `len(s) + Z_0(s) <= 100000`, where `Z_0(s)` is the number of `'z'` bytes in `s`. -/
  theorem spec_9 (s s' : Slice Std.U8) (t : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
      (h_lower : IsLowercase s)
      (h_t_ge : 2 ≤ t.val) (h_t_le : t.val ≤ 100000)
      (h_len_z : s.val.length + zCount (bytes s) ≤ 100000)
      (h_step : bytes s' = F (bytes s)) :
      ∀ r r' : Std.I64,
        length_after_transformations s t = ok r →
        length_after_transformations s' (i64Pred t) = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s s' : Slice Std.U8) (t : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 100000)
        (h_lower : IsLowercase s)
        (h_t_ge : 2 ≤ t.val) (h_t_le : t.val ≤ 100000)
        (h_len_z : s.val.length + zCount (bytes s) ≤ 100000)
        (h_step : bytes s' = F (bytes s)), ∀ r r' : Std.I64,
          length_after_transformations s t = ok r →
          length_after_transformations s' (i64Pred t) = ok r' →
          r.val = r'.val) := by
    sorry

  end AegisSpec.LengthAfterTransformations
