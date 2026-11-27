import Aegis.IsMatch.Code.Funs

/-!
# Specifications of `Aegis.IsMatch.is_match`

LeetCode problem `wildcard-matching`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsMatch

  def starByte : Std.U8 := 42#u8

  def questionByte : Std.U8 := 63#u8

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def IsPatternByte (b : Std.U8) : Prop := IsLowerByte b ∨ b.val = 63 ∨ b.val = 42

  def StepOK (b : Std.U8) (t : List Std.U8) (x y : ℕ) : Prop :=
    (b.val = 42 ∧ x ≤ y) ∨
      (b.val = 63 ∧ y = x + 1) ∨
        (97 ≤ b.val ∧ b.val ≤ 122 ∧ y = x + 1 ∧ ∃ h : x < t.length, t.get ⟨x, h⟩ = b)

  def WildcardMatches (q t : List Std.U8) : Prop :=
    ∃ a : ℕ → ℕ,
      a 0 = 0 ∧ a q.length = t.length ∧
        (∀ j : ℕ, j < q.length → a j ≤ a (j + 1)) ∧
          ∀ (j : ℕ) (hj : j < q.length), StepOK (q.get ⟨j, hj⟩) t (a j) (a (j + 1))

  def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => .nil
    | a :: l => .cons a (listNOfList l)

  theorem listNOfList_toList {α : Type} (l : List α) : (listNOfList l).toList = l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [show (listNOfList (a :: l)).toList = a :: (listNOfList l).toList from rfl, ih]

  def sliceOfList (l : List Std.U8) (h : l.length ≤ Usize.max) : Slice Std.U8 :=
    ⟨l.length, listNOfList l, h⟩

  @[simp]
  theorem sliceOfList_val (l : List Std.U8) (h : l.length ≤ Usize.max) :
      (sliceOfList l h).val = l := by
    show (listNOfList l).toList = l
    exact listNOfList_toList l

  theorem le_usize_max {n : ℕ} (h : n ≤ 2001) : n ≤ Usize.max := by
    have hmax : Usize.max = 2 ^ System.Platform.numBits - 1 := by
      simp [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits]
    rw [hmax]
    obtain hb | hb := System.Platform.numBits_eq
    · rw [hb]; omega
    · rw [hb]; omega

  def insertStarAt (p : List Std.U8) (i : ℕ) : List Std.U8 :=
    p.take i ++ starByte :: p.drop i

  theorem insertStarAt_length {p : List Std.U8} {i : ℕ} (hi : i ≤ p.length) :
      (insertStarAt p i).length = p.length + 1 := by
    simp only [insertStarAt, List.length_append, List.length_cons, List.length_take,
      List.length_drop, Nat.min_eq_left hi]
    omega

  def setAt (p : List Std.U8) (j : ℕ) (b : Std.U8) : List Std.U8 := p.set j b

  @[simp]
  theorem setAt_length (p : List Std.U8) (j : ℕ) (b : Std.U8) :
      (setAt p j b).length = p.length := List.length_set

  def eraseAt (p : List Std.U8) (j : ℕ) : List Std.U8 :=
    p.take (j + 1) ++ p.drop (j + 2)

  theorem eraseAt_length {p : List Std.U8} {j : ℕ} (hj : j + 1 < p.length) :
      (eraseAt p j).length = p.length - 1 := by
    simp only [eraseAt, List.length_append, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega : j + 1 ≤ p.length)]
    omega

  def insertStarSlice (p : Slice Std.U8) (i : ℕ) (hi : i ≤ p.val.length)
      (hp : p.val.length ≤ 1999) : Slice Std.U8 :=
    sliceOfList (insertStarAt p.val i) (le_usize_max (by rw [insertStarAt_length hi]; omega))

  @[simp]
  theorem insertStarSlice_val (p : Slice Std.U8) (i : ℕ) (hi : i ≤ p.val.length)
      (hp : p.val.length ≤ 1999) :
      (insertStarSlice p i hi hp).val = insertStarAt p.val i := by
    simp [insertStarSlice]

  def setByteSlice (p : Slice Std.U8) (j : ℕ) (b : Std.U8)
      (hp : p.val.length ≤ 2000) : Slice Std.U8 :=
    sliceOfList (setAt p.val j b) (le_usize_max (by rw [setAt_length]; omega))

  @[simp]
  theorem setByteSlice_val (p : Slice Std.U8) (j : ℕ) (b : Std.U8)
      (hp : p.val.length ≤ 2000) :
      (setByteSlice p j b hp).val = setAt p.val j b := by
    simp [setByteSlice]

  def eraseAtSlice (p : Slice Std.U8) (j : ℕ) (hj : j + 1 < p.val.length)
      (hp : p.val.length ≤ 2000) : Slice Std.U8 :=
    sliceOfList (eraseAt p.val j) (le_usize_max (by rw [eraseAt_length hj]; omega))

  @[simp]
  theorem eraseAtSlice_val (p : Slice Std.U8) (j : ℕ) (hj : j + 1 < p.val.length)
      (hp : p.val.length ≤ 2000) :
      (eraseAtSlice p j hj hp).val = eraseAt p.val j := by
    simp [eraseAtSlice]

  /-- Whenever is_match(s,p) returns a result r, r is true if and only if p wildcard-matches s, where p wildcard-matches s means: letting m = len(p), there exist integers a_0, ..., a_m such that a_0 = 0, a_m = len(s), 0 = a_0 <= a_1 <= ... <= a_m, and for every j with 0 <= j < m: if p[j] = '*' then a_{j+1} >= a_j; if p[j] = '?' then a_{j+1} = a_j + 1; and if p[j] is a lowercase letter then a_{j+1} = a_j + 1 and s[a_j] = p[j].
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 2000; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_1 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∀ r : Bool,
        Aegis.IsMatch.is_match s p = ok r → (r = true ↔ WildcardMatches p.val s.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∀ r : Bool,
          Aegis.IsMatch.is_match s p = ok r → (r = true ↔ WildcardMatches p.val s.val)) := by
    sorry

  /-- For every s and p satisfying the preconditions, is_match(s,p) returns a result r (either true or false) and does not fail.
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 2000; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_2 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∃ r : Bool, Aegis.IsMatch.is_match s p = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∃ r : Bool, Aegis.IsMatch.is_match s p = ok r) := by
    sorry

  /-- For every i with 0 <= i <= len(p), let q be the byte sequence of length len(p)+1 obtained by inserting '*' at position i: q[t] = p[t] for 0 <= t < i, q[i] = '*', and q[t] = p[t-1] for i < t < len(q). Whenever is_match(s,p) returns true, is_match(s,q) returns a result r_q and r_q is true.
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 1999; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_3 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 1999)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∀ (i : ℕ) (hi : i ≤ p.val.length),
        Aegis.IsMatch.is_match s p = ok true →
          ∃ r_q : Bool,
            Aegis.IsMatch.is_match s (insertStarSlice p i hi hp_len) = ok r_q ∧ r_q = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 1999)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∀ (i : ℕ) (hi : i ≤ p.val.length),
          Aegis.IsMatch.is_match s p = ok true →
            ∃ r_q : Bool,
              Aegis.IsMatch.is_match s (insertStarSlice p i hi hp_len) = ok r_q ∧ r_q = true) := by
    sorry

  /-- For every j with 0 <= j < len(p) such that p[j] is not '*', let q be p with q[j] = '*' and q[t] = p[t] for t != j. Whenever is_match(s,p) returns true, is_match(s,q) returns a result r_q and r_q is true.
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 2000; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_4 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∀ (j : ℕ) (hj : j < p.val.length), (p.val.get ⟨j, hj⟩).val ≠ 42 →
        Aegis.IsMatch.is_match s p = ok true →
          ∃ r_q : Bool,
            Aegis.IsMatch.is_match s (setByteSlice p j starByte hp_len) = ok r_q ∧
              r_q = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∀ (j : ℕ) (hj : j < p.val.length), (p.val.get ⟨j, hj⟩).val ≠ 42 →
          Aegis.IsMatch.is_match s p = ok true →
            ∃ r_q : Bool,
              Aegis.IsMatch.is_match s (setByteSlice p j starByte hp_len) = ok r_q ∧
                r_q = true) := by
    sorry

  /-- For every j with 0 <= j < len(p) such that p[j] is a lowercase letter, let q be p with q[j] = '?' and q[t] = p[t] for t != j. Whenever is_match(s,p) returns true, is_match(s,q) returns a result r_q and r_q is true.
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 2000; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_5 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∀ (j : ℕ) (hj : j < p.val.length), IsLowerByte (p.val.get ⟨j, hj⟩) →
        Aegis.IsMatch.is_match s p = ok true →
          ∃ r_q : Bool,
            Aegis.IsMatch.is_match s (setByteSlice p j questionByte hp_len) = ok r_q ∧
              r_q = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∀ (j : ℕ) (hj : j < p.val.length), IsLowerByte (p.val.get ⟨j, hj⟩) →
          Aegis.IsMatch.is_match s p = ok true →
            ∃ r_q : Bool,
              Aegis.IsMatch.is_match s (setByteSlice p j questionByte hp_len) = ok r_q ∧
                r_q = true) := by
    sorry

  /-- For every j with 0 <= j < len(p)-1 such that p[j] = '*' and p[j+1] = '*', let q be the byte sequence of length len(p)-1 obtained by deleting p[j+1]: q[t] = p[t] for 0 <= t <= j, and q[t] = p[t+1] for j < t < len(q). Whenever is_match(s,p) returns a result r and is_match(s,q) returns a result r_q, r = r_q.
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 2000; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_6 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∀ (j : ℕ) (hj : j < p.val.length - 1),
        (p.val.get ⟨j, by omega⟩).val = 42 →
          (p.val.get ⟨j + 1, by omega⟩).val = 42 →
            ∀ (r r_q : Bool),
              Aegis.IsMatch.is_match s p = ok r →
                Aegis.IsMatch.is_match s (eraseAtSlice p j (by omega) hp_len) = ok r_q →
                  r = r_q := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∀ (j : ℕ) (hj : j < p.val.length - 1),
          (p.val.get ⟨j, by omega⟩).val = 42 →
            (p.val.get ⟨j + 1, by omega⟩).val = 42 →
              ∀ (r r_q : Bool),
                Aegis.IsMatch.is_match s p = ok r →
                  Aegis.IsMatch.is_match s (eraseAtSlice p j (by omega) hp_len) = ok r_q →
                    r = r_q) := by
    sorry

  /-- For every j with 0 <= j < len(p) such that p[j] = '*', whenever is_match(s,p) returns a result r, r is true if and only if there exist integers a and b with 0 <= a <= b <= len(s) such that p[0:j] wildcard-matches s[0:a] and p[j+1:len(p)] wildcard-matches s[b:len(s)]. Here, for any pattern q and string t, 'q wildcard-matches t' means: letting m = len(q), there exist integers c_0, ..., c_m such that c_0 = 0, c_m = len(t), 0 = c_0 <= c_1 <= ... <= c_m, and for every k with 0 <= k < m: if q[k] = '*' then c_{k+1} >= c_k; if q[k] = '?' then c_{k+1} = c_k + 1; and if q[k] is a lowercase letter then c_{k+1} = c_k + 1 and t[c_k] = q[k].
    Preconditions: 0 <= len(s) <= 2000 and 0 <= len(p) <= 2000; every byte of s is a lowercase English letter (ASCII code 97 through 122 inclusive); every byte of p is either a lowercase English letter or '?' (ASCII 63) or '*' (ASCII 42). -/
  theorem spec_7 (s p : Slice Std.U8)
      (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
      (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b) :
      ∀ (j : ℕ) (hj : j < p.val.length), (p.val.get ⟨j, hj⟩).val = 42 →
        ∀ r : Bool,
          Aegis.IsMatch.is_match s p = ok r →
            (r = true ↔
              ∃ a b : ℕ,
                a ≤ b ∧ b ≤ s.val.length ∧
                  WildcardMatches (p.val.take j) (s.val.take a) ∧
                    WildcardMatches (p.val.drop (j + 1)) (s.val.drop b)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : s.val.length ≤ 2000) (hp_len : p.val.length ≤ 2000)
        (hs : ∀ b ∈ s.val, IsLowerByte b) (hp : ∀ b ∈ p.val, IsPatternByte b), ∀ (j : ℕ) (hj : j < p.val.length), (p.val.get ⟨j, hj⟩).val = 42 →
          ∀ r : Bool,
            Aegis.IsMatch.is_match s p = ok r →
              (r = true ↔
                ∃ a b : ℕ,
                  a ≤ b ∧ b ≤ s.val.length ∧
                    WildcardMatches (p.val.take j) (s.val.take a) ∧
                      WildcardMatches (p.val.drop (j + 1)) (s.val.drop b))) := by
    sorry

  end AegisSpec.IsMatch
