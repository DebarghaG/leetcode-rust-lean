import Aegis.MinValidStrings.Code.Funs

/-!
# Specifications of `Aegis.MinValidStrings.min_valid_strings`

LeetCode problem `minimum-number-of-valid-strings-to-form-target-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinValidStrings

  def IsLowerAscii (c : Std.U8) : Prop :=
    97 ≤ c.val ∧ c.val ≤ 122

  def Constraints (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) : Prop :=
    1 ≤ words.val.length ∧
    words.val.length ≤ 100 ∧
    (∀ (i : ℕ) (_hi : i < words.val.length),
        1 ≤ (words.val[i]'_hi).val.length ∧
        (words.val[i]'_hi).val.length ≤ 5000 ∧
        (∀ (j : ℕ) (hj : j < (words.val[i]'_hi).val.length),
          IsLowerAscii ((words.val[i]'_hi).val[j]'hj))) ∧
    (words.val.map (fun v => v.val.length)).sum ≤ 100000 ∧
    1 ≤ target.val.length ∧
    target.val.length ≤ 5000 ∧
    (∀ (j : ℕ) (hj : j < target.val.length), IsLowerAscii (target.val[j]'hj))

  def Seg (target : Slice Std.U8) (l r : ℕ) : List Std.U8 :=
    (target.val.drop l).take (r - l)

  def ValidSegment (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (l r : ℕ) :
      Prop :=
    0 ≤ l ∧ l < r ∧ r ≤ target.val.length ∧
    ∃ (i : ℕ) (hi : i < words.val.length),
      r - l ≤ (words.val[i]'hi).val.length ∧
      ∀ (j : ℕ), j < r - l → target.val[l + j]? = (words.val[i]'hi).val[j]?

  def PrefixSegment (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (l r : ℕ) :
      Prop :=
    0 ≤ l ∧ l < r ∧ r ≤ target.val.length ∧
    ∃ w : alloc.vec.Vec Std.U8, w ∈ words.val ∧ List.IsPrefix (Seg target l r) w.val

  theorem validSegment_iff_prefixSegment (words : Slice (alloc.vec.Vec Std.U8))
      (target : Slice Std.U8) (l r : ℕ) (h1 : 0 ≤ l) (h2 : l < r)
      (h3 : r ≤ target.val.length) :
      ValidSegment words target l r ↔ PrefixSegment words target l r := by
    have hlen : (Seg target l r).length = r - l := by
      simp only [Seg, List.length_take, List.length_drop]
      omega
    unfold ValidSegment PrefixSegment
    constructor
    · rintro ⟨-, -, -, i, hi, -, hget⟩
      refine ⟨h1, h2, h3, words.val[i]'hi, List.getElem_mem hi, ?_⟩
      rw [List.prefix_iff_eq_take, hlen]
      apply List.ext_getElem?
      intro j
      by_cases hj : j < r - l
      · simp only [Seg, List.getElem?_take, List.getElem?_drop, hj, ↓reduceIte]
        exact hget j hj
      · simp only [Seg, List.getElem?_take, hj, ↓reduceIte]
    · rintro ⟨-, -, -, w, hw, hp⟩
      rw [List.prefix_iff_eq_take] at hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
      have hle : r - l ≤ (words.val[i]).val.length := by
        have hpre : (Seg target l r) <+: (words.val[i]).val := by
          rw [List.prefix_iff_eq_take]
          exact hp
        have hlen' := List.IsPrefix.length_le hpre
        omega
      refine ⟨h1, h2, h3, i, hi, hle, ?_⟩
      intro j hj
      have hp' : Seg target l r = (words.val[i]).val.take (r - l) := by rw [hp, hlen]
      have h1' : (words.val[i]).val[j]? = (Seg target l r)[j]? := by
        rw [hp']
        simp only [List.getElem?_take, hj, ↓reduceIte]
      have h2' : (Seg target l r)[j]? = target.val[l + j]? := by
        simp only [Seg, List.getElem?_take, List.getElem?_drop, hj, ↓reduceIte]
      exact h2'.symm.trans h1'.symm

  def IsValidPartition (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (k : ℕ)
      (p : ℕ → ℕ) : Prop :=
    0 < k ∧ p 0 = 0 ∧ p k = target.val.length ∧
    (∀ t : ℕ, t < k → p t < p (t + 1)) ∧
    ∀ t : ℕ, t < k → ValidSegment words target (p t) (p (t + 1))

  def HasValidPartition (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (k : ℕ) :
      Prop :=
    ∃ p : ℕ → ℕ, IsValidPartition words target k p

  def IsPrefixPartition (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (k : ℕ)
      (p : ℕ → ℕ) : Prop :=
    0 < k ∧ p 0 = 0 ∧ p k = target.val.length ∧
    (∀ t : ℕ, t < k → p t < p (t + 1)) ∧
    ∀ t : ℕ, t < k → PrefixSegment words target (p t) (p (t + 1))

  def HasPrefixPartition (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (k : ℕ) : Prop :=
    ∃ p : ℕ → ℕ, IsPrefixPartition words target k p

  def IsValidString (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) : Prop :=
    ∃ (i : ℕ) (hi : i < words.val.length),
      target.val.length ≤ (words.val[i]'hi).val.length ∧
      ∀ (j : ℕ), j < target.val.length → target.val[j]? = (words.val[i]'hi).val[j]?

  def SomeWordStartsWithByteAt (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (p : ℕ) : Prop :=
    ∃ (i : ℕ) (hi : i < words.val.length), (words.val[i]'hi).val.head? = target.val[p]?

  def MaxWordLen (words : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
    (words.val.map (fun v => v.val.length)).foldr max 0

  def CeilDiv (n m : ℕ) : ℕ :=
    (n + m - 1) / m

  def IsPermutation (words2 words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    words2.val.length = words.val.length ∧
    ∃ f : ℕ → ℕ,
      (∀ (j : ℕ), j < words2.val.length → f j < words.val.length) ∧
      (∀ (i : ℕ), i < words.val.length → ∃ j : ℕ, j < words2.val.length ∧ f j = i) ∧
      (∀ (j : ℕ), j < words2.val.length → words2.val[j]? = words.val[f j]?)

  def WordsIncluded (words words2 : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ (i : ℕ) (hi : i < words.val.length),
      ∃ (j : ℕ) (hj : j < words2.val.length), words2.val[j]'hj = words.val[i]'hi

  theorem isValidString_iff_validSegment (words : Slice (alloc.vec.Vec Std.U8))
      (target : Slice Std.U8) (hn : 0 < target.val.length) :
      IsValidString words target ↔ ValidSegment words target 0 target.val.length := by
    unfold IsValidString ValidSegment
    constructor
    · rintro ⟨i, hi, hle, hget⟩
      refine ⟨Nat.zero_le _, hn, Nat.le_refl _, i, hi, ?_, ?_⟩
      · simpa using hle
      · intro j hj
        simpa using hget j (by simpa using hj)
    · rintro ⟨-, -, -, i, hi, hle, hget⟩
      refine ⟨i, hi, ?_, ?_⟩
      · simpa using hle
      · intro j hj
        simpa using hget j (by simpa using hj)

  /-- Define a segment target[l..r) to be valid iff 0 <= l < r <= len(target) and there exists i with 0 <= i < len(words) such that r-l <= len(words[i]) and for every j with 0 <= j < r-l, target[l+j] = words[i][j]. Define a valid partition into k strings to be indices 0 = p_0 < p_1 < ... < p_k = len(target) such that every segment target[p_t..p_{t+1}) for 0 <= t < k is valid. The function returns a result r (it does not fail), and r = -1 if no valid partition exists; otherwise r is the least k >= 1 for which a valid partition into k strings exists.
    Preconditions: Constraints hold: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 5000 and every byte of words[i] has ASCII code between 97 and 122; sum_{i=0}^{len(words)-1} len(words[i]) <= 100000; 1 <= len(target) <= 5000; every byte of target has ASCII code between 97 and 122. -/
  theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∃ r : Std.I64,
        Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
        ((∀ k : ℕ, 1 ≤ k → ¬ HasValidPartition words target k) ↔ r.val = -1) ∧
        (∀ k : ℕ, 1 ≤ k → (HasValidPartition words target k ↔ r.val ≤ (k : ℤ))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∃ r : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
          ((∀ k : ℕ, 1 ≤ k → ¬ HasValidPartition words target k) ↔ r.val = -1) ∧
          (∀ k : ℕ, 1 ≤ k → (HasValidPartition words target k ↔ r.val ≤ (k : ℤ)))) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(target).
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (target.val.length : ℤ)) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (target.val.length : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist indices 0 = p_0 < p_1 < ... < p_r = len(target) such that for every t with 0 <= t < r, the segment target[p_t..p_{t+1}) is valid: p_t < p_{t+1}, and there exists i with 0 <= i < len(words) such that p_{t+1}-p_t <= len(words[i]) and target[p_t+j] = words[i][j] for every j with 0 <= j < p_{t+1}-p_t.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        r.val ≠ -1 → ∃ p : ℕ → ℕ, IsValidPartition words target r.val.toNat p := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          r.val ≠ -1 → ∃ p : ℕ → ℕ, IsValidPartition words target r.val.toNat p) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every m >= 1 and every sequence of indices 0 = q_0 < q_1 < ... < q_m = len(target) such that each segment target[q_t..q_{t+1}) is a prefix of some word in words, we have r <= m.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        r.val ≠ -1 → ∀ (m : ℕ), 1 ≤ m → ∀ p : ℕ → ℕ,
          IsPrefixPartition words target m p → r.val ≤ (m : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          r.val ≠ -1 → ∀ (m : ℕ), 1 ≤ m → ∀ p : ℕ → ℕ,
            IsPrefixPartition words target m p → r.val ≤ (m : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 iff there do not exist k >= 1 and indices 0 = p_0 < p_1 < ... < p_k = len(target) such that every segment target[p_t..p_{t+1}) for 0 <= t < k is a prefix of some word in words.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        (r.val = -1 ↔ ¬ ∃ (k : ℕ) (p : ℕ → ℕ), IsPrefixPartition words target k p) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          (r.val = -1 ↔ ¬ ∃ (k : ℕ) (p : ℕ → ℕ), IsPrefixPartition words target k p)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 iff the whole target is a valid string, i.e., there exists i with 0 <= i < len(words) such that len(target) <= len(words[i]) and for every j with 0 <= j < len(target), target[j] = words[i][j].
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        (r.val = 1 ↔ IsValidString words target) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          (r.val = 1 ↔ IsValidString words target)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists i with 0 <= i < len(words) such that words[i][0] = target[0].
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        r.val ≠ -1 → SomeWordStartsWithByteAt words target 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          r.val ≠ -1 → SomeWordStartsWithByteAt words target 0) := by
    sorry

  /-- If len(target) = 1, then the function returns a result r with r = 1 if there exists i with 0 <= i < len(words) and words[i][0] = target[0], and r = -1 otherwise.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) (hlen : target.val.length = 1) :
      ∃ r : Std.I64,
        Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
        (SomeWordStartsWithByteAt words target 0 → r.val = 1) ∧
        (¬ SomeWordStartsWithByteAt words target 0 → r.val = -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target) (hlen : target.val.length = 1), ∃ r : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
          (SomeWordStartsWithByteAt words target 0 → r.val = 1) ∧
          (¬ SomeWordStartsWithByteAt words target 0 → r.val = -1)) := by
    sorry

  /-- If len(words[i]) = 1 for every i with 0 <= i < len(words), then the function returns a result r with r = len(target) if for every p with 0 <= p < len(target) there exists i with 0 <= i < len(words) and words[i][0] = target[p], and r = -1 otherwise.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target)
      (hone : ∀ (i : ℕ) (hi : i < words.val.length), (words.val[i]'hi).val.length = 1) :
      ∃ r : Std.I64,
        Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
        ((∀ p : ℕ, p < target.val.length → SomeWordStartsWithByteAt words target p) →
          r.val = (target.val.length : ℤ)) ∧
        (¬ (∀ p : ℕ, p < target.val.length → SomeWordStartsWithByteAt words target p) →
          r.val = -1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target)
        (hone : ∀ (i : ℕ) (hi : i < words.val.length), (words.val[i]'hi).val.length = 1), ∃ r : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
          ((∀ p : ℕ, p < target.val.length → SomeWordStartsWithByteAt words target p) →
            r.val = (target.val.length : ℤ)) ∧
          (¬ (∀ p : ℕ, p < target.val.length → SomeWordStartsWithByteAt words target p) →
            r.val = -1)) := by
    sorry

  /-- Let M be the maximum of len(words[i]) over all i with 0 <= i < len(words). Whenever the function returns a result r with r != -1, r >= ceil(len(target) / M).
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        r.val ≠ -1 →
        ((CeilDiv target.val.length (MaxWordLen words) : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          r.val ≠ -1 →
          ((CeilDiv target.val.length (MaxWordLen words) : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- If for every p with 0 <= p < len(target) there exists i with 0 <= i < len(words) such that len(words[i]) >= 1 and words[i][0] = target[p], then the function returns a result r with r != -1 and r <= len(target).
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_11 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target)
      (hcover : ∀ p : ℕ, p < target.val.length → SomeWordStartsWithByteAt words target p) :
      ∃ r : Std.I64,
        Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
        r.val ≠ -1 ∧ r.val ≤ (target.val.length : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target)
        (hcover : ∀ p : ℕ, p < target.val.length → SomeWordStartsWithByteAt words target p), ∃ r : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words target = ok r ∧
          r.val ≠ -1 ∧ r.val ≤ (target.val.length : ℤ)) := by
    sorry

  /-- If there exist a byte value b and an index p with 0 <= p < len(target) such that target[p] = b, and no word in words contains byte b (that is, for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), words[i][j] != b), then the function returns r = -1.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target)
      (b : Std.U8) (p : ℕ) (hp : p < target.val.length) (hb : target.val[p]'hp = b)
      (hno : ∀ (i : ℕ) (hi : i < words.val.length) (j : ℕ)
        (hj : j < (words.val[i]'hi).val.length), (words.val[i]'hi).val[j]'hj ≠ b) :
      ∃ r : Std.I64,
        Aegis.MinValidStrings.min_valid_strings words target = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target)
        (b : Std.U8) (p : ℕ) (hp : p < target.val.length) (hb : target.val[p]'hp = b)
        (hno : ∀ (i : ℕ) (hi : i < words.val.length) (j : ℕ)
          (hj : j < (words.val[i]'hi).val.length), (words.val[i]'hi).val[j]'hj ≠ b), ∃ r : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words target = ok r ∧ r.val = -1) := by
    sorry

  /-- Let words2 be any other list of byte strings satisfying the constraints stated in the preconditions such that for every i with 0 <= i < len(words) there exists j with 0 <= j < len(words2) and words2[j] = words[i]. If min_valid_strings words target returns r with r != -1, and min_valid_strings words2 target returns r2, then r2 != -1 and r2 <= r.
    Preconditions: 1 <= len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 5000 and every byte of words[i] has ASCII code between 97 and 122; sum_{i=0}^{len(words)-1} len(words[i]) <= 100000; 1 <= len(target) <= 5000; every byte of target has ASCII code between 97 and 122; words2 is a list of byte strings with 1 <= len(words2) <= 100, for every j with 0 <= j < len(words2), 1 <= len(words2[j]) <= 5000 and every byte of words2[j] has ASCII code between 97 and 122, and sum_{j=0}^{len(words2)-1} len(words2[j]) <= 100000; for every i with 0 <= i < len(words), there exists j with 0 <= j < len(words2) and words2[j] = words[i]. -/
  theorem spec_13 (words words2 : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) (hC2 : Constraints words2 target)
      (hsub : WordsIncluded words words2) :
      ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
        r.val ≠ -1 → ∀ r2 : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words2 target = ok r2 →
            r2.val ≠ -1 ∧ r2.val ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (words words2 : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target) (hC2 : Constraints words2 target)
        (hsub : WordsIncluded words words2), ∀ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r →
          r.val ≠ -1 → ∀ r2 : Std.I64,
            Aegis.MinValidStrings.min_valid_strings words2 target = ok r2 →
              r2.val ≠ -1 ∧ r2.val ≤ r.val) := by
    sorry

  /-- If the function returns r on (words, target) and r2 on (words2, target), then r = r2.
    Preconditions: Constraints hold for words and target. Let words2 be a permutation of words: len(words2) = len(words) and there is a bijection f from {0,...,len(words2)-1} to {0,...,len(words)-1} such that words2[j] = words[f(j)] for every j with 0 <= j < len(words2). -/
  theorem spec_14 (words words2 : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) (hperm : IsPermutation words2 words) :
      ∀ r r2 : Std.I64,
        Aegis.MinValidStrings.min_valid_strings words target = ok r →
        Aegis.MinValidStrings.min_valid_strings words2 target = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (words words2 : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target) (hperm : IsPermutation words2 words), ∀ r r2 : Std.I64,
          Aegis.MinValidStrings.min_valid_strings words target = ok r →
          Aegis.MinValidStrings.min_valid_strings words2 target = ok r2 → r.val = r2.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail by arithmetic overflow or panic.
    Preconditions: Constraints hold as in spec_1. -/
  theorem spec_15 (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hC : Constraints words target) :
      ∃ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hC : Constraints words target), ∃ r : Std.I64, Aegis.MinValidStrings.min_valid_strings words target = ok r) := by
    sorry

  end AegisSpec.MinValidStrings
