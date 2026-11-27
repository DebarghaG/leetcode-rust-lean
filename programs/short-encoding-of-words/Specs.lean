import Aegis.MinimumLengthEncoding.Code.Funs

/-!
# Specifications of `Aegis.MinimumLengthEncoding.minimum_length_encoding`

LeetCode problem `short-encoding-of-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumLengthEncoding

  namespace AegisSpec.MinimumLengthEncoding

  def wordsList (words : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
    words.val.map (fun v => v.val)

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def hashByte : Std.U8 := UScalar.ofNatCore 35 (by norm_num)

  def IsSuffix (w v : List Std.U8) : Prop :=
    ∃ (hle : w.length ≤ v.length),
      ∀ (k : Nat) (hk : k < w.length), w[k] = v[v.length - w.length + k]

  def IsProperSuffix (w v : List Std.U8) : Prop :=
    w.length < v.length ∧ IsSuffix w v

  noncomputable def keptWords (ws : List (List Std.U8)) : Finset (List Std.U8) := by
    classical
    exact ws.toFinset.filter (fun w => ∀ (j : Nat) (hj : j < ws.length), ¬ IsProperSuffix w ws[j])

  noncomputable def encodingCost (ws : List (List Std.U8)) : Nat :=
    (keptWords ws).sum (fun w => w.length + 1)

  def naiveCost (ws : List (List Std.U8)) : Nat :=
    (ws.map (fun w => w.length + 1)).sum

  noncomputable def distinctFirstBytes (ws : List (List Std.U8)) : Nat :=
    (ws.filterMap (fun w => w.head?)).toFinset.card

  def SpellsAt (s : List Std.U8) (p : Nat) (w : List Std.U8) : Prop :=
    ∀ (t : Nat) (ht : t < w.length), s[p + t]? = some w[t]

  def BlockAt (s : List Std.U8) (p : Nat) (w : List Std.U8) : Prop :=
    p < s.length ∧
    s[p]? ≠ some hashByte ∧
    SpellsAt s p w ∧
    s[p + w.length]? = some hashByte ∧
    (∀ (k : Nat), p ≤ k → k < p + w.length → s[k]? ≠ some hashByte)

  def IsValidEncoding (ws : List (List Std.U8)) (s : List Std.U8) (indices : List Nat) : Prop :=
    indices.length = ws.length ∧
    1 ≤ s.length ∧
    s[s.length - 1]? = some hashByte ∧
    ∀ (i : Nat) (hi : i < ws.length),
      ∃ (p : Nat), indices[i]? = some p ∧ BlockAt s p (ws[i])

  /-- Let a byte string w be a proper suffix of a byte string v when len(w) < len(v) and for every k with 0 <= k < len(w), w[k] = v[len(v)-len(w)+k]. Let U be the set of byte strings w such that (a) words[i] = w for some i with 0 <= i < n, and (b) w is not a proper suffix of words[j] for any j with 0 <= j < n. Then the function returns a result r and r = sum_{w in U} (len(w) + 1).
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          r.val = (encodingCost (wordsList words) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            r.val = (encodingCost (wordsList words) : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, panic, or go out of bounds on any input satisfying the preconditions.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64, minimum_length_encoding words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64, minimum_length_encoding words = ok r) := by
    sorry

  /-- The function returns a result r and there exist a byte string s and an array indices of length n such that: s is nonempty and s[len(s)-1] = '#'; and for every i with 0 <= i < n, 0 <= indices[i] < len(s), s[indices[i]] != '#', and there exists k such that indices[i] <= k < len(s), s[k] = '#', for every k' with indices[i] <= k' < k, s[k'] != '#', indices[i] + len(words[i]) = k, and for every t with 0 <= t < len(words[i]), s[indices[i]+t] = words[i][t]; and len(s) = r.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          ∃ (s : List Std.U8) (indices : List Nat),
            IsValidEncoding (wordsList words) s indices ∧ r.val = (s.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            ∃ (s : List Std.U8) (indices : List Nat),
              IsValidEncoding (wordsList words) s indices ∧ r.val = (s.length : ℤ)) := by
    sorry

  /-- The function returns a result r and for every byte string s and every array indices of length n satisfying the valid-encoding conditions (s ends with '#', and for every i with 0 <= i < n the substring of s starting at indices[i] and ending just before the next '#' equals words[i]), it holds that len(s) >= r.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          ∀ (s : List Std.U8) (indices : List Nat),
            IsValidEncoding (wordsList words) s indices → r.val ≤ (s.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            ∀ (s : List Std.U8) (indices : List Nat),
              IsValidEncoding (wordsList words) s indices → r.val ≤ (s.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{n-1} (len(words[i]) + 1).
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          r.val ≤ (naiveCost (wordsList words) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            r.val ≤ (naiveCost (wordsList words) : ℤ)) := by
    sorry

  /-- The function returns a result r and for every i with 0 <= i < n, r >= len(words[i]) + 1.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          ∀ (i : Nat) (hi : i < words.length),
            ((words.val[i]).val.length + 1 : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            ∀ (i : Nat) (hi : i < words.length),
              ((words.val[i]).val.length + 1 : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r. If for every i and j with 0 <= i < n, 0 <= j < n, and i != j, words[i] is not a suffix of words[j] (where a is a suffix of b if len(a) <= len(b) and for every k with 0 <= k < len(a), a[k] = b[len(b)-len(a)+k]), then r = sum_{i=0}^{n-1} (len(words[i]) + 1).
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          ((∀ (i j : Nat) (hi : i < words.length) (hj : j < words.length), i ≠ j →
              ¬ IsSuffix ((words.val[i]).val) ((words.val[j]).val)) →
            r.val = (naiveCost (wordsList words) : ℤ)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            ((∀ (i j : Nat) (hi : i < words.length) (hj : j < words.length), i ≠ j →
                ¬ IsSuffix ((words.val[i]).val) ((words.val[j]).val)) →
              r.val = (naiveCost (wordsList words) : ℤ))) := by
    sorry

  /-- The function returns a result r and if len(words[i]) = 1 for every i with 0 <= i < n, then r = 2 * |{ b | b is a byte and there exists i with words[i][0] = b }|.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          ((∀ (i : Nat) (hi : i < words.length), (words.val[i]).val.length = 1) →
            r.val = 2 * (distinctFirstBytes (wordsList words) : ℤ)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            ((∀ (i : Nat) (hi : i < words.length), (words.val[i]).val.length = 1) →
              r.val = 2 * (distinctFirstBytes (wordsList words) : ℤ))) := by
    sorry

  /-- The function returns a result r. If there exists j with 0 <= j < n such that for every i with 0 <= i < n, words[i] is a suffix of words[j] (where a is a suffix of b if len(a) <= len(b) and for every k with 0 <= k < len(a), a[k] = b[len(b)-len(a)+k]), then r = len(words[j]) + 1.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          (∀ (j : Nat) (hj : j < words.length)
              (hs : ∀ (i : Nat) (hi : i < words.length),
                IsSuffix ((words.val[i]).val) ((words.val[j]).val)),
            r.val = ((words.val[j]).val.length + 1 : ℤ)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            (∀ (j : Nat) (hj : j < words.length)
                (hs : ∀ (i : Nat) (hi : i < words.length),
                  IsSuffix ((words.val[i]).val) ((words.val[j]).val)),
              r.val = ((words.val[j]).val.length + 1 : ℤ))) := by
    sorry

  /-- Let words' be words with w appended at the end. If r = minimum_length_encoding(words) and r' = minimum_length_encoding(words'), then r' = r.
    Preconditions: Let n = len(words). Preconditions: 1 <= n < 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). Let w be a byte string with 1 <= len(w) <= 7 and every byte of w an ASCII lowercase letter, and suppose there exists j with 0 <= j < n such that w is a suffix of words[j]. -/
  theorem spec_10 (words words' : Slice (alloc.vec.Vec Std.U8)) (w : List Std.U8)
      (hn_pos : 1 ≤ words.length) (hn_lt : words.length < 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t])))
      (hw_pos : 1 ≤ w.length) (hw_le : w.length ≤ 7)
      (hw_bytes : ∀ (t : Nat) (ht : t < w.length), IsLowerByte w[t])
      (hw_suffix : ∃ (j : Nat) (hj : j < words.length), IsSuffix w (words.val[j]).val)
      (hwords' : wordsList words' = wordsList words ++ [w])
      (r r' : Std.I64)
      (hr : minimum_length_encoding words = ok r)
      (hr' : minimum_length_encoding words' = ok r') :
      r' = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (w : List Std.U8)
        (hn_pos : 1 ≤ words.length) (hn_lt : words.length < 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t])))
        (hw_pos : 1 ≤ w.length) (hw_le : w.length ≤ 7)
        (hw_bytes : ∀ (t : Nat) (ht : t < w.length), IsLowerByte w[t])
        (hw_suffix : ∃ (j : Nat) (hj : j < words.length), IsSuffix w (words.val[j]).val)
        (hwords' : wordsList words' = wordsList words ++ [w])
        (r r' : Std.I64)
        (hr : minimum_length_encoding words = ok r)
        (hr' : minimum_length_encoding words' = ok r'), r' = r) := by
    sorry

  /-- For every array words2 of byte strings with len(words2) = n such that there exists a permutation π of {0,...,n-1} with words2[i] = words[π(i)] for every i with 0 <= i < n, if r = minimum_length_encoding(words) and r2 = minimum_length_encoding(words2), then r2 = r.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_11 (words words2 : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t])))
      (hlen2 : words2.val.length = words.length)
      (hperm : ∃ π : Fin words.length → Fin words.length,
        Function.Bijective π ∧
          ∀ (i : Nat) (hi : i < words.length),
            (words2.val[i]).val = (words.val[(π ⟨i, hi⟩).val]'(π ⟨i, hi⟩).isLt).val)
      (r r2 : Std.I64)
      (hr : minimum_length_encoding words = ok r)
      (hr2 : minimum_length_encoding words2 = ok r2) :
      r2 = r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words words2 : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t])))
        (hlen2 : words2.val.length = words.length)
        (hperm : ∃ π : Fin words.length → Fin words.length,
          Function.Bijective π ∧
            ∀ (i : Nat) (hi : i < words.length),
              (words2.val[i]).val = (words.val[(π ⟨i, hi⟩).val]'(π ⟨i, hi⟩).isLt).val)
        (r r2 : Std.I64)
        (hr : minimum_length_encoding words = ok r)
        (hr2 : minimum_length_encoding words2 = ok r2), r2 = r) := by
    sorry

  /-- Let words' be words with w appended at the end. If r = minimum_length_encoding(words) and r' = minimum_length_encoding(words'), then r' >= r.
    Preconditions: Let n = len(words). Preconditions: 1 <= n < 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). Let w be a byte string with 1 <= len(w) <= 7 and every byte of w an ASCII lowercase letter. -/
  theorem spec_12 (words words' : Slice (alloc.vec.Vec Std.U8)) (w : List Std.U8)
      (hn_pos : 1 ≤ words.length) (hn_lt : words.length < 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t])))
      (hw_pos : 1 ≤ w.length) (hw_le : w.length ≤ 7)
      (hw_bytes : ∀ (t : Nat) (ht : t < w.length), IsLowerByte w[t])
      (hwords' : wordsList words' = wordsList words ++ [w])
      (r r' : Std.I64)
      (hr : minimum_length_encoding words = ok r)
      (hr' : minimum_length_encoding words' = ok r') :
      r ≤ r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8)) (w : List Std.U8)
        (hn_pos : 1 ≤ words.length) (hn_lt : words.length < 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t])))
        (hw_pos : 1 ≤ w.length) (hw_le : w.length ≤ 7)
        (hw_bytes : ∀ (t : Nat) (ht : t < w.length), IsLowerByte w[t])
        (hwords' : wordsList words' = wordsList words ++ [w])
        (r r' : Std.I64)
        (hr : minimum_length_encoding words = ok r)
        (hr' : minimum_length_encoding words' = ok r'), r ≤ r') := by
    sorry

  /-- The function returns a result r and 2 <= r <= 16000.
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_13 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧ 2 ≤ r.val ∧ r.val ≤ 16000 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧ 2 ≤ r.val ∧ r.val ≤ 16000) := by
    sorry

  /-- The function returns a result r. If there exist i and j with 0 <= i < n, 0 <= j < n such that words[i] is a proper suffix of words[j] (len(words[i]) < len(words[j]) and for every k with 0 <= k < len(words[i]), words[i][k] = words[j][len(words[j])-len(words[i])+k]), then r < sum_{t=0}^{n-1} (len(words[t]) + 1).
    Preconditions: Let n = len(words). Preconditions: 1 <= n <= 2000; for every i with 0 <= i < n, 1 <= len(words[i]) <= 7 and every byte of words[i] is an ASCII lowercase letter (byte value between 97 and 122). -/
  theorem spec_14 (words : Slice (alloc.vec.Vec Std.U8))
      (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
      (hwords : ∀ (i : Nat) (hi : i < words.length),
        1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
          (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
            IsLowerByte ((words.val[i]).val[t]))) :
      ∃ r : Std.I64,
        minimum_length_encoding words = ok r ∧
          ((∃ (i j : Nat) (hi : i < words.length) (hj : j < words.length),
              IsProperSuffix ((words.val[i]).val) ((words.val[j]).val)) →
            r.val < (naiveCost (wordsList words) : ℤ)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (hn_pos : 1 ≤ words.length) (hn_le : words.length ≤ 2000)
        (hwords : ∀ (i : Nat) (hi : i < words.length),
          1 ≤ (words.val[i]).val.length ∧ (words.val[i]).val.length ≤ 7 ∧
            (∀ (t : Nat) (ht : t < (words.val[i]).val.length),
              IsLowerByte ((words.val[i]).val[t]))), ∃ r : Std.I64,
          minimum_length_encoding words = ok r ∧
            ((∃ (i j : Nat) (hi : i < words.length) (hj : j < words.length),
                IsProperSuffix ((words.val[i]).val) ((words.val[j]).val)) →
              r.val < (naiveCost (wordsList words) : ℤ))) := by
    sorry

  end AegisSpec.MinimumLengthEncoding
