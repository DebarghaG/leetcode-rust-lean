import Aegis.ShortestWay.Code.Funs

/-!
# Specifications of `Aegis.ShortestWay.shortest_way`

LeetCode problem `shortest-way-to-form-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ShortestWay

  def IsLower (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def AllLower (l : List U8) : Prop := ∀ b ∈ l, IsLower b

  def Occurs (src : List U8) (b : U8) : Prop := ∃ j : Fin src.length, src[j] = b

  def segment (t : List U8) (l e : ℕ) : List U8 := (t.drop l).take (e - l)

  def IsSubsequence (seg src : List U8) : Prop :=
    ∃ idx : ℕ → ℕ,
      (∀ t, t < seg.length → src[idx t]? = seg[t]?) ∧
      (∀ t u, t < u → u < seg.length → idx t < idx u)

  def Good (source target : Slice U8) (l e : ℕ) : Prop :=
    IsSubsequence (segment target.val l e) source.val

  def Decomposable (source target : Slice U8) (k : ℕ) : Prop :=
    ∃ c : ℕ → ℕ,
      c 0 = 0 ∧ c k = target.val.length ∧
        (∀ j, j < k → c j < c (j + 1)) ∧
        (∀ j, j < k → Good source target (c j) (c (j + 1)))

  def NoLaterPair (src : List U8) (a b : U8) : Prop :=
    ¬ ∃ j : Fin src.length, ∃ k : Fin src.length, j < k ∧ src[j] = a ∧ src[k] = b

  /-- The function returns Ok ans (i.e. it does not fail), where ans is the minimum number of subsequences of source whose concatenation equals target. Equivalently, let n = len(target). Call a contiguous segment target[l..e) (0 <= l <= e <= n) good when it is a subsequence of source, meaning that either e = l, or there are indices 0 <= i_l < i_{l+1} < ... < i_{e-1} < len(source) with source[i_t] = target[t] for every t in [l,e). A decomposition into k parts is a sequence 0 = c_0 < c_1 < ... < c_k = n such that target[c_j..c_{j+1}) is good for every j with 0 <= j < k. Then ans is the least k for which such a decomposition exists; if no decomposition exists, ans = -1. Since target is nonempty in the precondition, any valid decomposition has k >= 1 and all parts are nonempty.
    Preconditions: source and target are byte slices of lowercase English letters with 1 <= len(source) <= 1000 and 1 <= len(target) <= 1000. -/
  theorem spec_1 (source target : Slice U8)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_pos : 1 ≤ source.val.length) (hsrc_bound : source.val.length ≤ 1000)
      (htgt_pos : 1 ≤ target.val.length) (htgt_bound : target.val.length ≤ 1000) :
      ∃ r : I64,
        Aegis.ShortestWay.shortest_way source target = ok r ∧
          ((∃ k : ℕ,
              Decomposable source target k ∧ r.val = (k : ℤ) ∧
                ∀ k' : ℕ, Decomposable source target k' → k ≤ k') ∨
            ((¬ ∃ k : ℕ, Decomposable source target k) ∧ r.val = -1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_pos : 1 ≤ source.val.length) (hsrc_bound : source.val.length ≤ 1000)
        (htgt_pos : 1 ≤ target.val.length) (htgt_bound : target.val.length ≤ 1000), ∃ r : I64,
          Aegis.ShortestWay.shortest_way source target = ok r ∧
            ((∃ k : ℕ,
                Decomposable source target k ∧ r.val = (k : ℤ) ∧
                  ∀ k' : ℕ, Decomposable source target k' → k ≤ k') ∨
              ((¬ ∃ k : ℕ, Decomposable source target k) ∧ r.val = -1))) := by
    sorry

  /-- The function returns Ok r for some i64 r; it does not panic, overflow, return Err, or otherwise fail.
    Preconditions: source and target are byte slices with len(source) <= 1000 and len(target) <= 1000. No lowercase or nonemptiness assumption is needed. -/
  theorem spec_2 (source target : Slice U8)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000) :
      ∃ r : I64, Aegis.ShortestWay.shortest_way source target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000), ∃ r : I64, Aegis.ShortestWay.shortest_way source target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there exists an index i with 0 <= i < len(target) such that target[i] is different from source[j] for every j with 0 <= j < len(source).
    Preconditions: source and target are byte slices of lowercase English letters with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_3 (source target : Slice U8)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      (r.val = -1 ↔ ∃ (i : ℕ) (_ : i < target.val.length), ¬ Occurs source.val target.val[i]) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), (r.val = -1 ↔ ∃ (i : ℕ) (_ : i < target.val.length), ¬ Occurs source.val target.val[i])) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, r <= len(target).
    Preconditions: source and target are byte slices of lowercase English letters with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_4 (source target : Slice U8)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r)
      (hr_nonneg : 0 ≤ r.val) :
      r.val ≤ (target.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r)
        (hr_nonneg : 0 ≤ r.val), r.val ≤ (target.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with len(target) > 0 and r >= 0, r >= 1.
    Preconditions: source and target are byte slices of lowercase English letters with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_5 (source target : Slice U8)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r)
      (htgt_pos : 0 < target.val.length) (hr_nonneg : 0 ≤ r.val) :
      1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r)
        (htgt_pos : 0 < target.val.length) (hr_nonneg : 0 ≤ r.val), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if len(target) = 0.
    Preconditions: source and target are byte slices with len(source) <= 1000 and len(target) <= 1000. -/
  theorem spec_6 (source target : Slice U8)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      (r.val = 0 ↔ target.val.length = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), (r.val = 0 ↔ target.val.length = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if target is a subsequence of source, i.e. there exist indices 0 <= i_0 < i_1 < ... < i_{len(target)-1} < len(source) such that source[i_j] = target[j] for every j with 0 <= j < len(target).
    Preconditions: source and target are byte slices with len(target) > 0 and len(source), len(target) <= 1000. -/
  theorem spec_7 (source target : Slice U8)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (htgt_pos : 0 < target.val.length)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      (r.val = 1 ↔ IsSubsequence target.val source.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (htgt_pos : 0 < target.val.length)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), (r.val = 1 ↔ IsSubsequence target.val source.val)) := by
    sorry

  /-- Whenever the function returns a result r, if target is not a subsequence of source (i.e. there do not exist 0 <= i_0 < ... < i_{len(target)-1} < len(source) with source[i_j] = target[j] for all j), then r >= 2.
    Preconditions: source and target are byte slices with len(target) > 0, len(source), len(target) <= 1000, and for every i with 0 <= i < len(target) there exists j with 0 <= j < len(source) and source[j] = target[i]. -/
  theorem spec_8 (source target : Slice U8)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (htgt_pos : 0 < target.val.length)
      (hall : ∀ (i : ℕ) (_ : i < target.val.length), Occurs source.val target.val[i])
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r)
      (hnot : ¬ IsSubsequence target.val source.val) :
      2 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (htgt_pos : 0 < target.val.length)
        (hall : ∀ (i : ℕ) (_ : i < target.val.length), Occurs source.val target.val[i])
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r)
        (hnot : ¬ IsSubsequence target.val source.val), 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = n if and only if both of the following hold: for every i with 0 <= i < n there exists j with 0 <= j < len(source) and source[j] = target[i]; and for every i with 0 <= i < n-1 there do not exist indices 0 <= j < k < len(source) with source[j] = target[i] and source[k] = target[i+1].
    Preconditions: source and target are byte slices of lowercase English letters with len(target) = n >= 1 and len(source) <= 1000. -/
  theorem spec_9 (source target : Slice U8) (n : ℕ)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_bound : source.val.length ≤ 1000)
      (hn : target.val.length = n) (hn_pos : 1 ≤ n)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      (r.val = (n : ℤ) ↔
        ((∀ (i : ℕ) (_ : i < n), Occurs source.val target.val[i]) ∧
          (∀ (i : ℕ) (_ : i + 1 < n),
            NoLaterPair source.val target.val[i] target.val[i + 1]))) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (source target : Slice U8) (n : ℕ)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_bound : source.val.length ≤ 1000)
        (hn : target.val.length = n) (hn_pos : 1 ≤ n)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), (r.val = (n : ℤ) ↔
          ((∀ (i : ℕ) (_ : i < n), Occurs source.val target.val[i]) ∧
            (∀ (i : ℕ) (_ : i + 1 < n),
              NoLaterPair source.val target.val[i] target.val[i + 1])))) := by
    sorry

  /-- Whenever the function returns a result r, if target[i] = c for every i with 0 <= i < n, then r is the least integer k with n <= k*m; otherwise r = -1.
    Preconditions: source and target are byte slices with len(source) = m > 0, len(target) = n <= 1000, and there exists a byte c such that source[j] = c for every j with 0 <= j < m. -/
  theorem spec_10 (source target : Slice U8) (m n : ℕ) (c : U8)
      (hm : source.val.length = m) (hn : target.val.length = n)
      (hm_pos : 0 < m) (hn_bound : n ≤ 1000)
      (hconst : ∀ (j : ℕ) (_ : j < m), source.val[j] = c)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      ((∀ (i : ℕ) (_ : i < n), target.val[i] = c) →
          ((n : ℤ) ≤ r.val * (m : ℤ) ∧ ∀ z : ℤ, (n : ℤ) ≤ z * (m : ℤ) → r.val ≤ z)) ∧
        ((¬ ∀ (i : ℕ) (_ : i < n), target.val[i] = c) → r.val = -1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (source target : Slice U8) (m n : ℕ) (c : U8)
        (hm : source.val.length = m) (hn : target.val.length = n)
        (hm_pos : 0 < m) (hn_bound : n ≤ 1000)
        (hconst : ∀ (j : ℕ) (_ : j < m), source.val[j] = c)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), ((∀ (i : ℕ) (_ : i < n), target.val[i] = c) →
            ((n : ℤ) ≤ r.val * (m : ℤ) ∧ ∀ z : ℤ, (n : ℤ) ≤ z * (m : ℤ) → r.val ≤ z)) ∧
          ((¬ ∀ (i : ℕ) (_ : i < n), target.val[i] = c) → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r with r = k >= 0, there exist cut points 0 = c_0 < c_1 < ... < c_k = len(target) such that for every j with 0 <= j < k, the segment target[c_j..c_{j+1}) is a subsequence of source, meaning there are indices 0 <= i_{c_j} < i_{c_j+1} < ... < i_{c_{j+1}-1} < len(source) with source[i_t] = target[t] for every t in [c_j,c_{j+1}).
    Preconditions: source and target are byte slices of lowercase English letters with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_11 (source target : Slice U8)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      ∀ k : ℕ, r.val = (k : ℤ) → Decomposable source target k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), ∀ k : ℕ, r.val = (k : ℤ) → Decomposable source target k) := by
    sorry

  /-- Whenever the function returns a result r with r = k >= 0, for every j with 0 <= j < k there does not exist a decomposition of target into j subsequences of source, i.e. there are no cut points 0 = d_0 < d_1 < ... < d_j = len(target) such that every segment target[d_t..d_{t+1}) is a subsequence of source.
    Preconditions: source and target are byte slices of lowercase English letters with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_12 (source target : Slice U8)
      (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      ∀ k : ℕ, r.val = (k : ℤ) → ∀ j : ℕ, j < k → ¬ Decomposable source target j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_lower : AllLower source.val) (htgt_lower : AllLower target.val)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), ∀ k : ℕ, r.val = (k : ℤ) → ∀ j : ℕ, j < k → ¬ Decomposable source target j) := by
    sorry

  /-- The function returns Ok r (it never fails), and r >= 0 if and only if every byte of target occurs at least once in source. Consequently r = -1 if and only if some target byte does not occur in source; in particular, r >= 0 when len(target) = 0.
    Preconditions: source and target are byte slices with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_13 (source target : Slice U8)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000) :
      ∃ r : I64,
        Aegis.ShortestWay.shortest_way source target = ok r ∧
          (0 ≤ r.val ↔ ∀ (i : ℕ) (_ : i < target.val.length), Occurs source.val target.val[i]) ∧
          (r.val = -1 ↔ ∃ (i : ℕ) (_ : i < target.val.length), ¬ Occurs source.val target.val[i]) ∧
          (target.val.length = 0 → 0 ≤ r.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000), ∃ r : I64,
          Aegis.ShortestWay.shortest_way source target = ok r ∧
            (0 ≤ r.val ↔ ∀ (i : ℕ) (_ : i < target.val.length), Occurs source.val target.val[i]) ∧
            (r.val = -1 ↔ ∃ (i : ℕ) (_ : i < target.val.length), ¬ Occurs source.val target.val[i]) ∧
            (target.val.length = 0 → 0 ≤ r.val)) := by
    sorry

  /-- Whenever the function returns Ok r, if target can be partitioned into k contiguous segments, each a subsequence of source (i.e. there exist 0 = c_0 < c_1 < ... < c_k = len(target) such that each segment target[c_j..c_{j+1}) is a subsequence of source, with k = 0 allowed only when len(target) = 0), then 0 <= r <= k. In particular, if such a decomposition exists then r != -1, and if no such decomposition exists then r = -1.
    Preconditions: source and target are byte slices with len(source) <= 1000 and len(target) <= 1000; empty slices are allowed. -/
  theorem spec_14 (source target : Slice U8)
      (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
      (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r) :
      (∀ k : ℕ, Decomposable source target k → 0 ≤ r.val ∧ r.val ≤ (k : ℤ)) ∧
        ((¬ ∃ k : ℕ, Decomposable source target k) → r.val = -1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (source target : Slice U8)
        (hsrc_bound : source.val.length ≤ 1000) (htgt_bound : target.val.length ≤ 1000)
        (r : I64) (hr : Aegis.ShortestWay.shortest_way source target = ok r), (∀ k : ℕ, Decomposable source target k → 0 ≤ r.val ∧ r.val ≤ (k : ℤ)) ∧
          ((¬ ∃ k : ℕ, Decomposable source target k) → r.val = -1)) := by
    sorry

  end AegisSpec.ShortestWay
