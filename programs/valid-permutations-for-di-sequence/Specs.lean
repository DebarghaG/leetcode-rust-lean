import Aegis.NumPermsDiSequence.Code.Funs

/-!
# Specifications of `Aegis.NumPermsDiSequence.num_perms_di_sequence`

LeetCode problem `valid-permutations-for-di-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.NumPermsDiSequence

  def MOD : ℕ := 1000000007

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def IsDI (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, b.val = 68 ∨ b.val = 73

  def IsPermOf (m : ℕ) (p : List ℕ) : Prop :=
    p.length = m + 1 ∧ (∀ x ∈ p, x ≤ m) ∧ p.Nodup

  def Compatible (s p : List ℕ) : Prop :=
    ∀ (i a b : ℕ), p[i]? = some a → p[i+1]? = some b →
      (s[i]? = some 68 → b < a) ∧ (s[i]? = some 73 → a < b)

  noncomputable def validPerms (s : List ℕ) : Finset (List ℕ) := by
    classical
    exact (List.range (s.length + 1)).permutations.toFinset.filter
      (fun p => IsPermOf s.length p ∧ Compatible s p)

  noncomputable def C (s : List ℕ) : ℕ := (validPerms s).card

  def compVal (c : ℕ) : ℕ := if c = 68 then 73 else if c = 73 then 68 else c

  def compSig (s : List ℕ) : List ℕ := s.map compVal

  def alternatingSig (n : ℕ) : List ℕ :=
    (List.range n).map (fun j => if j % 2 = 0 then 73 else 68)

  noncomputable def EulerZigzag (m : ℕ) : ℕ := C (alternatingSig (m - 1))

  def numDescents (p : List ℕ) : ℕ := (p.zip p.tail).countP (fun q => decide (q.2 < q.1))

  noncomputable def eulerian (m k : ℕ) : ℕ := by
    classical
    exact ((List.range m).permutations.toFinset.filter (fun p => numDescents p = k)).card

  def countOf (c : ℕ) (l : List ℕ) : ℕ := (l.filter (fun x => decide (x = c))).length

  def allDISigs : ℕ → List (List ℕ)
    | 0 => [[]]
    | n + 1 =>
      (allDISigs n).map (fun t => 68 :: t) ++ (allDISigs n).map (fun t => 73 :: t)

  /-- Let n = len(s). Let C(s) be the number of permutations p of the set {0,1,...,n} (equivalently, lists p of length n+1 containing each of 0,1,...,n exactly once) such that for every i with 0 <= i < n, if s[i] = 68 then p[i] > p[i+1], and if s[i] = 73 then p[i] < p[i+1]. Whenever num_perms_di_sequence returns a result r, r is congruent to C(s) modulo M = 1000000007.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). -/
  theorem spec_1 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
        Int.ModEq 1000000007 r.val (C (bytes s) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
          Int.ModEq 1000000007 r.val (C (bytes s) : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, num_perms_di_sequence returns a result r; it does not fail, panic, or encounter arithmetic overflow.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). -/
  theorem spec_2 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s) :
      ∃ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s), ∃ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r) := by
    sorry

  /-- Whenever num_perms_di_sequence returns a result r, 0 <= r < 1000000007.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). -/
  theorem spec_3 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Whenever num_perms_di_sequence returns a result r, r = 1.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). Assume either s[i] = 73 for all i with 0 <= i < n, or s[i] = 68 for all i with 0 <= i < n. -/
  theorem spec_4 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s)
      (hconst : (∀ i, i < s.length → (bytes s)[i]? = some 73) ∨
        ∀ i, i < s.length → (bytes s)[i]? = some 68) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r → r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s)
        (hconst : (∀ i, i < s.length → (bytes s)[i]? = some 73) ∨
          ∀ i, i < s.length → (bytes s)[i]? = some 68), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r → r.val = 1) := by
    sorry

  /-- Let E_m be the Euler zigzag number: the number of permutations a of {0,1,...,m-1} such that for every j with 0 <= j < m-1, a[j] < a[j+1] when j is even and a[j] > a[j+1] when j is odd. Then whenever num_perms_di_sequence returns r, r is congruent to E_{n+1} modulo 1000000007.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). Assume s is alternating: either s[i] = 73 exactly for even i and s[i] = 68 exactly for odd i, or s[i] = 68 exactly for even i and s[i] = 73 exactly for odd i, for all 0 <= i < n. -/
  theorem spec_5 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s)
      (halt : bytes s = alternatingSig s.length ∨
        bytes s = compSig (alternatingSig s.length)) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
        Int.ModEq 1000000007 r.val (EulerZigzag (s.length + 1) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s)
        (halt : bytes s = alternatingSig s.length ∨
          bytes s = compSig (alternatingSig s.length)), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
          Int.ModEq 1000000007 r.val (EulerZigzag (s.length + 1) : ℤ)) := by
    sorry

  /-- Let rev(s) be the byte array t of length n with t[i] = s[n-1-i] for 0 <= i < n, and let C(s) and C(t) be the corresponding valid-permutation counts as defined in spec_1. Then C(s) = C(t). Equivalently, if the function returns r_s on s and r_t on rev(s), then r_s = r_t.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). -/
  theorem spec_6 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s) :
      C (bytes s) = C (bytes s).reverse ∧
        ∀ (t : Slice Std.U8), bytes t = (bytes s).reverse →
          ∀ r_s r_t : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r_s →
            Aegis.NumPermsDiSequence.num_perms_di_sequence t = ok r_t → r_s = r_t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s), C (bytes s) = C (bytes s).reverse ∧
          ∀ (t : Slice Std.U8), bytes t = (bytes s).reverse →
            ∀ r_s r_t : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r_s →
              Aegis.NumPermsDiSequence.num_perms_di_sequence t = ok r_t → r_s = r_t) := by
    sorry

  /-- Let comp(s) be the byte array t with t[i] = 73 if s[i] = 68, and t[i] = 68 if s[i] = 73, for 0 <= i < n. Let C(s) and C(t) be the corresponding valid-permutation counts as defined in spec_1. Then C(s) = C(t). Equivalently, if the function returns r_s on s and r_t on comp(s), then r_s = r_t.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). -/
  theorem spec_7 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s) :
      C (bytes s) = C (compSig (bytes s)) ∧
        ∀ (t : Slice Std.U8), bytes t = compSig (bytes s) →
          ∀ r_s r_t : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r_s →
            Aegis.NumPermsDiSequence.num_perms_di_sequence t = ok r_t → r_s = r_t := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s), C (bytes s) = C (compSig (bytes s)) ∧
          ∀ (t : Slice Std.U8), bytes t = compSig (bytes s) →
            ∀ r_s r_t : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r_s →
              Aegis.NumPermsDiSequence.num_perms_di_sequence t = ok r_t → r_s = r_t) := by
    sorry

  /-- Whenever num_perms_di_sequence returns a result r, r equals the exact number C(s) of valid permutations as defined in spec_1, not merely C(s) modulo 1000000007.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). Assume n <= 11. -/
  theorem spec_8 (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
      (hdi : IsDI s) (hshort : s.length ≤ 11) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
        r.val = (C (bytes s) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.length) (hlen' : s.length ≤ 200)
        (hdi : IsDI s) (hshort : s.length ≤ 11), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
          r.val = (C (bytes s) : ℤ)) := by
    sorry

  /-- Whenever num_perms_di_sequence returns r, r is congruent modulo 1000000007 to binom(n+1, k+1) - 1, where binom(a,b) is the ordinary binomial coefficient.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). Assume there is exactly one index k with 0 <= k < n such that s[k] = 68, and s[i] = 73 for every i with 0 <= i < n and i != k. -/
  theorem spec_9 (s : Slice Std.U8) (k : ℕ) (hlen : 1 ≤ s.length)
      (hlen' : s.length ≤ 200) (hdi : IsDI s) (hk : k < s.length)
      (hsingle : ∀ i : ℕ, i < s.length → ((bytes s)[i]? = some 68 ↔ i = k)) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
        Int.ModEq 1000000007 r.val (((s.length + 1).choose (k + 1) : ℕ) - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (k : ℕ) (hlen : 1 ≤ s.length)
        (hlen' : s.length ≤ 200) (hdi : IsDI s) (hk : k < s.length)
        (hsingle : ∀ i : ℕ, i < s.length → ((bytes s)[i]? = some 68 ↔ i = k)), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
          Int.ModEq 1000000007 r.val (((s.length + 1).choose (k + 1) : ℕ) - 1)) := by
    sorry

  /-- Whenever num_perms_di_sequence returns r, r is congruent modulo 1000000007 to binom(n+1, k+1) - 1.
    Preconditions: Let n = len(s). 1 <= n <= 200, and for every i with 0 <= i < n, s[i] is either 68 (ASCII 'D') or 73 (ASCII 'I'). Assume there is exactly one index k with 0 <= k < n such that s[k] = 73, and s[i] = 68 for every i with 0 <= i < n and i != k. -/
  theorem spec_10 (s : Slice Std.U8) (k : ℕ) (hlen : 1 ≤ s.length)
      (hlen' : s.length ≤ 200) (hdi : IsDI s) (hk : k < s.length)
      (hsingle : ∀ i : ℕ, i < s.length → ((bytes s)[i]? = some 73 ↔ i = k)) :
      ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
        Int.ModEq 1000000007 r.val (((s.length + 1).choose (k + 1) : ℕ) - 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (k : ℕ) (hlen : 1 ≤ s.length)
        (hlen' : s.length ≤ 200) (hdi : IsDI s) (hk : k < s.length)
        (hsingle : ∀ i : ℕ, i < s.length → ((bytes s)[i]? = some 73 ↔ i = k)), ∀ r : Std.I64, Aegis.NumPermsDiSequence.num_perms_di_sequence s = ok r →
          Int.ModEq 1000000007 r.val (((s.length + 1).choose (k + 1) : ℕ) - 1)) := by
    sorry

  end AegisSpec.NumPermsDiSequence
