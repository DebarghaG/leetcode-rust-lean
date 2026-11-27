import Aegis.BeautifulSubstrings.Code.Funs

/-!
# Specifications of `Aegis.BeautifulSubstrings.beautiful_substrings`

LeetCode problem `count-beautiful-substrings-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.BeautifulSubstrings

  namespace AegisSpec.BeautifulSubstrings

  def IsVowel (c : Std.U8) : Prop :=
    c.val = 97 ∨ c.val = 101 ∨ c.val = 105 ∨ c.val = 111 ∨ c.val = 117

  def isVowel (c : Std.U8) : Bool :=
    c.val == 97 || c.val == 101 || c.val == 105 || c.val == 111 || c.val == 117

  def V (l : List Std.U8) (i j : Nat) : Int :=
    ((List.countP isVowel ((l.drop i).take (j - i)) : Nat) : Int)

  def C (l : List Std.U8) (i j : Nat) : Int :=
    ((j : Int) - (i : Int)) - V l i j

  def IsBeautiful (l : List Std.U8) (k : Int) (i j : Nat) : Prop :=
    V l i j = C l i j ∧ (V l i j * C l i j) % k = 0

  instance decidableIsBeautiful (l : List Std.U8) (k : Int) (i j : Nat) :
      Decidable (IsBeautiful l k i j) :=
    inferInstanceAs (Decidable (V l i j = C l i j ∧ (V l i j * C l i j) % k = 0))

  def beautifulPairSet (l : List Std.U8) (k : Int) : Finset (Nat × Nat) :=
    ((Finset.range (l.length + 1)).product (Finset.range (l.length + 1))).filter
      (fun p : Nat × Nat => p.1 < p.2 ∧ IsBeautiful l k p.1 p.2)

  def beautifulCount (l : List Std.U8) (k : Int) : Nat :=
    (beautifulPairSet l k).card

  def IsReverse (rev s : Slice Std.U8) : Prop :=
    rev.val = s.val.reverse

  def SameVowelPattern (s t : Slice Std.U8) : Prop :=
    ∀ (u : Nat) (a b : Std.U8), s.val[u]? = some a → t.val[u]? = some b → (IsVowel a ↔ IsVowel b)

  /-- The function returns a result r and r equals the number of pairs (i, j) of integers with 0 <= i < j <= len(s) such that the substring s[i..j) is beautiful, where for such a pair we define V(i,j) = the number of indices t with i <= t < j and s[t] in {97, 101, 105, 111, 117} (the ASCII codes of 'a','e','i','o','u'), C(i,j) = (j - i) - V(i,j), and s[i..j) is called beautiful iff V(i,j) = C(i,j) and (V(i,j) * C(i,j)) mod k = 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122 (s is an ASCII lowercase English word); 1 <= k <= 1000. -/
  theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
      ∃ r : Std.I64,
        beautiful_substrings s k = ok r ∧ r.val = (beautifulCount s.val k.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64,
          beautiful_substrings s k = ok r ∧ r.val = (beautifulCount s.val k.val : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, beautiful_substrings returns some result r; it does not fail, overflow, or panic.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000) :
      ∃ r : Std.I64, beautiful_substrings s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000), ∃ r : Std.I64, beautiful_substrings s k = ok r) := by
    sorry

  /-- Whenever beautiful_substrings returns a result r, we have r >= 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (r : Std.I64) (hr : beautiful_substrings s k = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (r : Std.I64) (hr : beautiful_substrings s k = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever beautiful_substrings returns a result r, we have r <= len(s) * (len(s) + 1) / 2.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (r : Std.I64) (hr : beautiful_substrings s k = ok r) :
      r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (r : Std.I64) (hr : beautiful_substrings s k = ok r), r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- If len(s) = 0, then beautiful_substrings returns 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hempty : s.val.length = 0) :
      ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hempty : s.val.length = 0), ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0) := by
    sorry

  /-- If len(s) = 1, then beautiful_substrings returns 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hone : s.val.length = 1) :
      ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hone : s.val.length = 1), ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever beautiful_substrings returns a result r with r > 0, there exists at least one pair (i, j) with 0 <= i < j <= len(s) such that V(i,j) = C(i,j) and (V(i,j) * C(i,j)) mod k = 0, where V(i,j) is the number of t with i <= t < j and s[t] in {97, 101, 105, 111, 117} and C(i,j) = (j - i) - V(i,j).
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_7 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (r : Std.I64) (hr : beautiful_substrings s k = ok r) (hpos : 0 < r.val) :
      ∃ i j : Nat, i < j ∧ j ≤ s.val.length ∧ IsBeautiful s.val k.val i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (r : Std.I64) (hr : beautiful_substrings s k = ok r) (hpos : 0 < r.val), ∃ i j : Nat, i < j ∧ j ≤ s.val.length ∧ IsBeautiful s.val k.val i j) := by
    sorry

  /-- Whenever beautiful_substrings returns a result r with r = 0, for every pair (i, j) with 0 <= i < j <= len(s) we have that V(i,j) != C(i,j) or (V(i,j) * C(i,j)) mod k != 0, where V(i,j) is the number of t with i <= t < j and s[t] in {97, 101, 105, 111, 117} and C(i,j) = (j - i) - V(i,j).
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (r : Std.I64) (hr : beautiful_substrings s k = ok r) (hzero : r.val = 0) :
      ∀ i j : Nat, i < j → j ≤ s.val.length → ¬ IsBeautiful s.val k.val i j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (r : Std.I64) (hr : beautiful_substrings s k = ok r) (hzero : r.val = 0), ∀ i j : Nat, i < j → j ≤ s.val.length → ¬ IsBeautiful s.val k.val i j) := by
    sorry

  /-- If every byte s[t] with 0 <= t < len(s) is not in {97, 101, 105, 111, 117} (that is, every character is a consonant), then beautiful_substrings returns 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000; len(s) >= 1. -/
  theorem spec_9 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hlen1 : 1 ≤ s.val.length)
      (hconsonants : ∀ c ∈ s.val, ¬ IsVowel c) :
      ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hlen1 : 1 ≤ s.val.length)
        (hconsonants : ∀ c ∈ s.val, ¬ IsVowel c), ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0) := by
    sorry

  /-- If every byte s[t] with 0 <= t < len(s) is in {97, 101, 105, 111, 117} (that is, every character is a vowel), then beautiful_substrings returns 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000; len(s) >= 1. -/
  theorem spec_10 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hlen1 : 1 ≤ s.val.length)
      (hvowels : ∀ c ∈ s.val, IsVowel c) :
      ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hlen1 : 1 ≤ s.val.length)
        (hvowels : ∀ c ∈ s.val, IsVowel c), ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0) := by
    sorry

  /-- Let m = floor(len(s) / 2). If k > m * m, then beautiful_substrings returns 0.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000; len(s) >= 2. -/
  theorem spec_11 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hlen2 : 2 ≤ s.val.length)
      (hbig : (((s.val.length / 2) * (s.val.length / 2) : Nat) : Int) < k.val) :
      ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hlen2 : 2 ≤ s.val.length)
        (hbig : (((s.val.length / 2) * (s.val.length / 2) : Nat) : Int) < k.val), ∃ r : Std.I64, beautiful_substrings s k = ok r ∧ r.val = 0) := by
    sorry

  /-- If beautiful_substrings(s, d) returns r_d and beautiful_substrings(s, k) returns r_k, then r_k <= r_d.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; d and k are integers with 1 <= d <= 1000, 1 <= k <= 1000, and d divides k (k = d * t for some integer t). -/
  theorem spec_12 (s : Slice Std.U8) (d k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hd : 1 ≤ d.val ∧ d.val ≤ 1000)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hdvd : ∃ t : Int, k.val = d.val * t)
      (r_d r_k : Std.I64)
      (hrd : beautiful_substrings s d = ok r_d)
      (hrk : beautiful_substrings s k = ok r_k) :
      r_k.val ≤ r_d.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (d k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hd : 1 ≤ d.val ∧ d.val ≤ 1000)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hdvd : ∃ t : Int, k.val = d.val * t)
        (r_d r_k : Std.I64)
        (hrd : beautiful_substrings s d = ok r_d)
        (hrk : beautiful_substrings s k = ok r_k), r_k.val ≤ r_d.val) := by
    sorry

  /-- Let rev be the string with len(rev) = len(s) and rev[u] = s[len(s) - 1 - u] for all u with 0 <= u < len(s). If beautiful_substrings(s, k) returns r and beautiful_substrings(rev, k) returns r', then r = r'.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_13 (s rev : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (hrev : IsReverse rev s)
      (r r' : Std.I64)
      (hr : beautiful_substrings s k = ok r)
      (hr' : beautiful_substrings rev k = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s rev : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (hrev : IsReverse rev s)
        (r r' : Std.I64)
        (hr : beautiful_substrings s k = ok r)
        (hr' : beautiful_substrings rev k = ok r'), r.val = r'.val) := by
    sorry

  /-- If beautiful_substrings(s, k) returns r_s and beautiful_substrings(t, k) returns r_t, then r_s = r_t. Equivalently, the answer depends only on the vowel/consonant pattern of s and on k, not on which particular vowel or consonant occupies each position.
    Preconditions: 0 <= len(s) <= 50000; 0 <= len(t) <= 50000; len(s) = len(t); every byte of s and t is in 97..122; for every u with 0 <= u < len(s), s[u] is in {97,101,105,111,117} iff t[u] is in {97,101,105,111,117}; 1 <= k <= 1000. -/
  theorem spec_14 (s t : Slice Std.U8) (k : Std.I64)
      (hlength_s : s.val.length ≤ 50000)
      (hlength_t : t.val.length ≤ 50000)
      (hlen : s.val.length = t.val.length)
      (hbytes_s : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hbytes_t : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hpat : SameVowelPattern s t)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (r_s r_t : Std.I64)
      (hr_s : beautiful_substrings s k = ok r_s)
      (hr_t : beautiful_substrings t k = ok r_t) :
      r_s.val = r_t.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
        (hlength_s : s.val.length ≤ 50000)
        (hlength_t : t.val.length ≤ 50000)
        (hlen : s.val.length = t.val.length)
        (hbytes_s : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hbytes_t : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hpat : SameVowelPattern s t)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (r_s r_t : Std.I64)
        (hr_s : beautiful_substrings s k = ok r_s)
        (hr_t : beautiful_substrings t k = ok r_t), r_s.val = r_t.val) := by
    sorry

  /-- Whenever beautiful_substrings(s, k) returns a result r, we have r <= floor(len(s)/2) * floor((len(s)+1)/2). This is the number of non-empty even-length substrings of s, since every beautiful substring has V = C and therefore even length.
    Preconditions: 0 <= len(s) <= 50000; every byte s[t] with 0 <= t < len(s) satisfies 97 <= s[t] <= 122; 1 <= k <= 1000. -/
  theorem spec_15 (s : Slice Std.U8) (k : Std.I64)
      (hlength : s.val.length ≤ 50000)
      (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
      (r : Std.I64) (hr : beautiful_substrings s k = ok r) :
      r.val ≤ (((s.val.length / 2) * ((s.val.length + 1) / 2) : Nat) : Int) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlength : s.val.length ≤ 50000)
        (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hk : 1 ≤ k.val ∧ k.val ≤ 1000)
        (r : Std.I64) (hr : beautiful_substrings s k = ok r), r.val ≤ (((s.val.length / 2) * ((s.val.length + 1) / 2) : Nat) : Int)) := by
    sorry

  section SanityChecks

  end SanityChecks

  end AegisSpec.BeautifulSubstrings
