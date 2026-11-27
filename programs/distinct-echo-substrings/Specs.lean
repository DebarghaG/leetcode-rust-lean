import Aegis.DistinctEchoSubstrings.Code.Funs

/-!
# Specifications of `Aegis.DistinctEchoSubstrings.distinct_echo_substrings`

LeetCode problem `distinct-echo-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DistinctEchoSubstrings

  namespace AegisSpec.DistinctEchoSubstrings

  def lowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def IsSubstr (s t : List Std.U8) : Prop :=
    ∃ i L : Nat, i + L ≤ t.length ∧ s = (t.drop i).take L

  def substrOf (t : List Std.U8) (i j : Nat) : List Std.U8 := (t.drop i).take (j - i)

  def IsEcho (s : List Std.U8) : Prop :=
    2 ≤ s.length ∧ s.length % 2 = 0 ∧ s.drop (s.length / 2) = s.take (s.length / 2)

  def echoSubstrings (t : List Std.U8) : Set (List Std.U8) :=
    {s | IsSubstr s t ∧ IsEcho s}

  def IsEchoOcc (t : List Std.U8) (i L : Nat) : Prop :=
    1 ≤ L ∧ i + 2 * L ≤ t.length ∧ ∀ k, k < L → t[i + k]? = t[i + L + k]?

  def doubledBytes (t : List Std.U8) : Set Std.U8 :=
    {c | ∃ i, i + 1 < t.length ∧ t[i]? = some c ∧ t[i + 1]? = some c}

  def evenIntervalCount (n : Nat) : Nat :=
    Finset.sum (Finset.Icc 1 (n / 2)) (fun L => n - 2 * L + 1)

  def bytesToSlice (l : List Std.U8) : Slice Std.U8 :=
    if h : l.length ≤ Usize.max then ⟨l.length, listNOf l, h⟩
    else ⟨0, Aeneas.Data.ListN.ListN.nil, Nat.zero_le _⟩
  where
    listNOf : (l : List Std.U8) → Aeneas.Data.ListN.ListN Std.U8 l.length
      | [] => .nil
      | a :: l => .cons a (listNOf l)

  def EchoOcc (t : List Std.U8) : Type := {p : Nat × Nat // IsEchoOcc t p.1 p.2}

  def echoOccSetoid (t : List Std.U8) : Setoid (EchoOcc t) where
    r p q := p.1.2 = q.1.2 ∧ ∀ k, k < 2 * p.1.2 → t[p.1.1 + k]? = t[q.1.1 + k]?
    iseqv :=
      ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩,
       fun {_ _} h => ⟨h.1.symm, fun k hk => (h.2 k (by rw [h.1]; exact hk)).symm⟩,
       fun {_ _ _} h₁ h₂ =>
         ⟨h₁.1.trans h₂.1,
          fun k hk => (h₁.2 k hk).trans (h₂.2 k (by rw [← h₁.1]; exact hk))⟩⟩

  /-- For every byte list text satisfying the preconditions, let s be a byte list. Say s is a contiguous substring of text if there exist integers i,j with 0 <= i <= j <= len(text), len(s)=j-i, and s[k]=text[i+k] for every k with 0 <= k < len(s). Say a byte list s is an echo if len(s) is even, len(s)>=2, and s[k]=s[len(s)/2+k] for every k with 0 <= k < len(s)/2. The function returns Ok r, and r equals the cardinality of the set of byte lists s such that s is a contiguous substring of text and s is an echo; two byte lists are identified in this set exactly when they have the same length and the same byte at every index, so each echo substring string is counted once regardless of how many times it occurs, and no other string is counted.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code (97 <= text[i] <= 122 for every i with 0 <= i < len(text)). -/
  theorem spec_1 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧
          r.val = ((echoSubstrings text.val).ncard : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧
            r.val = ((echoSubstrings text.val).ncard : ℤ)) := by
    sorry

  /-- For every text satisfying the preconditions, the function returns a result r; it does not panic, access out of bounds, or overflow while computing the returned i64.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code (97 <= text[i] <= 122 for every i with 0 <= i < len(text)). -/
  theorem spec_2 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∃ r : Std.I64, distinct_echo_substrings text = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∃ r : Std.I64, distinct_echo_substrings text = ok r) := by
    sorry

  /-- Let n=len(text). Whenever the function returns a result r, 0 <= r <= M, where M = sum over L=1..floor(n/2) of (n-2L+1), with an empty sum when n<2. Here M is the total number of even-length contiguous index intervals [i,i+2L) in text.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_3 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∀ r : Std.I64, distinct_echo_substrings text = ok r →
        0 ≤ r.val ∧ r.val ≤ (evenIntervalCount text.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∀ r : Std.I64, distinct_echo_substrings text = ok r →
          0 ≤ r.val ∧ r.val ≤ (evenIntervalCount text.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r=0.
    Preconditions: len(text)=0; the lowercase-byte condition is vacuous. -/
  theorem spec_4 (text : Slice Std.U8) (hlen : text.val.length = 0) :
      ∃ r : Std.I64, distinct_echo_substrings text = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length = 0), ∃ r : Std.I64, distinct_echo_substrings text = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and: r=1 if text[0]=text[1], and r=0 if text[0]!=text[1].
    Preconditions: len(text)=2 and both bytes are lowercase ASCII letters. -/
  theorem spec_5 (text : Slice Std.U8) (a b : Std.U8) (htext : text.val = [a, b])
      (ha : lowerByte a) (hb : lowerByte b) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧ r.val = (if a = b then 1 else 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (text : Slice Std.U8) (a b : Std.U8) (htext : text.val = [a, b])
        (ha : lowerByte a) (hb : lowerByte b), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧ r.val = (if a = b then 1 else 0)) := by
    sorry

  /-- The function returns a result r and: r=1 if text[0]=text[1] or text[1]=text[2], and r=0 otherwise.
    Preconditions: len(text)=3 and all bytes are lowercase ASCII letters. -/
  theorem spec_6 (text : Slice Std.U8) (a b c : Std.U8) (htext : text.val = [a, b, c])
      (ha : lowerByte a) (hb : lowerByte b) (hc : lowerByte c) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧
          r.val = (if a = b ∨ b = c then 1 else 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (text : Slice Std.U8) (a b c : Std.U8) (htext : text.val = [a, b, c])
        (ha : lowerByte a) (hb : lowerByte b) (hc : lowerByte c), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧
            r.val = (if a = b ∨ b = c then 1 else 0)) := by
    sorry

  /-- Let n=len(text). The function returns a result r and r = floor(n/2) (integer division n div 2).
    Preconditions: Let n=len(text). We have 1 <= n <= 2000, and there is a byte c with 97 <= c <= 122 such that text[i]=c for every i with 0 <= i < n. -/
  theorem spec_7 (text : Slice Std.U8) (c : Std.U8) (hn : 1 ≤ text.val.length)
      (hn' : text.val.length ≤ 2000) (hc : lowerByte c)
      (hconst : ∀ b ∈ text.val, b = c) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧ r.val = ((text.val.length / 2 : Nat) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (text : Slice Std.U8) (c : Std.U8) (hn : 1 ≤ text.val.length)
        (hn' : text.val.length ≤ 2000) (hc : lowerByte c)
        (hconst : ∀ b ∈ text.val, b = c), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧ r.val = ((text.val.length / 2 : Nat) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r>0 if and only if there exist integers i,L such that L>=1, 0<=i, i+2L<=len(text), and text[i+k]=text[i+L+k] for every k with 0<=k<L.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_8 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∀ r : Std.I64, distinct_echo_substrings text = ok r →
        (0 < r.val ↔ ∃ i L : Nat, IsEchoOcc text.val i L) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∀ r : Std.I64, distinct_echo_substrings text = ok r →
          (0 < r.val ↔ ∃ i L : Nat, IsEchoOcc text.val i L)) := by
    sorry

  /-- Let B be the set of bytes c for which there exists i with 0 <= i and i+1 < len(text) and text[i]=text[i+1]=c. Whenever the function returns a result r, r >= the number of elements of B.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_9 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∀ r : Std.I64, distinct_echo_substrings text = ok r →
        ((doubledBytes text.val).ncard : ℤ) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∀ r : Std.I64, distinct_echo_substrings text = ok r →
          ((doubledBytes text.val).ncard : ℤ) ≤ r.val) := by
    sorry

  /-- Let rev(text) be the byte list of length len(text) defined by rev(text)[i]=text[len(text)-1-i] for 0<=i<len(text). The function returns a result r, and if r_rev is the result of distinct_echo_substrings on rev(text), then r = r_rev.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_10 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∃ r r_rev : Std.I64,
        distinct_echo_substrings text = ok r ∧
          distinct_echo_substrings (bytesToSlice text.val.reverse) = ok r_rev ∧
            r = r_rev := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∃ r r_rev : Std.I64,
          distinct_echo_substrings text = ok r ∧
            distinct_echo_substrings (bytesToSlice text.val.reverse) = ok r_rev ∧
              r = r_rev) := by
    sorry

  /-- For every pair of integers i,j with 0 <= i <= j <= len(text), let u be the contiguous byte list with len(u)=j-i and u[k]=text[i+k] for 0<=k<j-i. Define a distinct echo substring of u to be a non-empty byte list s that is a contiguous substring of u and equals a+a for some non-empty byte list a, counted once by content. The function returns r and r is at least the number of distinct echo substrings of u. Equivalently, every distinct echo substring of u is also a distinct echo substring of text.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_11 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧
          ∀ i j : Nat, i ≤ j → j ≤ text.val.length →
            ((echoSubstrings (substrOf text.val i j)).ncard : ℤ) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧
            ∀ i j : Nat, i ≤ j → j ≤ text.val.length →
              ((echoSubstrings (substrOf text.val i j)).ncard : ℤ) ≤ r.val) := by
    sorry

  /-- Let B be the set of bytes c for which there exists i with 0 <= i <= 2 and text[i]=text[i+1]=c, and let |B| be its cardinality. The function returns a result r and r = |B| + (1 if text[0]=text[2] and text[1]=text[3], else 0).
    Preconditions: len(text)=4 and all bytes are lowercase ASCII letters. -/
  theorem spec_12 (text : Slice Std.U8) (a b c d : Std.U8) (htext : text.val = [a, b, c, d])
      (hlower : ∀ x ∈ text.val, lowerByte x) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧
          r.val = ((doubledBytes text.val).ncard : ℤ) +
            (if a = c ∧ b = d then 1 else 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (text : Slice Std.U8) (a b c d : Std.U8) (htext : text.val = [a, b, c, d])
        (hlower : ∀ x ∈ text.val, lowerByte x), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧
            r.val = ((doubledBytes text.val).ncard : ℤ) +
              (if a = c ∧ b = d then 1 else 0)) := by
    sorry

  /-- For every bijection f from the 26 lowercase ASCII codes to themselves, let f(text) be the byte list with f(text)[i]=f(text[i]) for 0<=i<len(text). If r_f is the result of distinct_echo_substrings on f(text), then the function returns r and r = r_f.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_13 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) (g : Std.U8 → Std.U8)
      (hg_lower : ∀ b : Std.U8, lowerByte b → lowerByte (g b))
      (hg_inj : ∀ b₁ b₂ : Std.U8, lowerByte b₁ → lowerByte b₂ → g b₁ = g b₂ → b₁ = b₂) :
      ∃ r r_g : Std.I64,
        distinct_echo_substrings text = ok r ∧
          distinct_echo_substrings (bytesToSlice (text.val.map g)) = ok r_g ∧
            r = r_g := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b) (g : Std.U8 → Std.U8)
        (hg_lower : ∀ b : Std.U8, lowerByte b → lowerByte (g b))
        (hg_inj : ∀ b₁ b₂ : Std.U8, lowerByte b₁ → lowerByte b₂ → g b₁ = g b₂ → b₁ = b₂), ∃ r r_g : Std.I64,
          distinct_echo_substrings text = ok r ∧
            distinct_echo_substrings (bytesToSlice (text.val.map g)) = ok r_g ∧
              r = r_g) := by
    sorry

  /-- Define an echo occurrence in text to be a pair (i,L) such that L>=1, 0<=i, i+2L<=len(text), and text[i+k]=text[i+L+k] for every 0<=k<L. Define two such occurrences (i,L) and (j,L') to be equivalent when L=L' and text[i+k]=text[j+k] for every 0<=k<2L. The function returns r and r equals the number of equivalence classes of echo occurrences under this relation.
    Preconditions: 0 <= len(text) <= 2000 and every byte of text is an ASCII lowercase letter code. -/
  theorem spec_14 (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
      (hlower : ∀ b ∈ text.val, lowerByte b) :
      ∃ r : Std.I64,
        distinct_echo_substrings text = ok r ∧
          r.val = (Nat.card (Quot (echoOccSetoid text.val)) : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (text : Slice Std.U8) (hlen : text.val.length ≤ 2000)
        (hlower : ∀ b ∈ text.val, lowerByte b), ∃ r : Std.I64,
          distinct_echo_substrings text = ok r ∧
            r.val = (Nat.card (Quot (echoOccSetoid text.val)) : ℤ)) := by
    sorry

  end AegisSpec.DistinctEchoSubstrings
