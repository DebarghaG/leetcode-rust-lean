import Aegis.MinLength.Code.Funs

/-!
# Specifications of `Aegis.MinLength.min_length`

LeetCode problem `smallest-substring-with-identical-characters-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinLength

  abbrev zeroByte : U8 := 48#u8

  abbrev oneByte : U8 := 49#u8

  def isBit (b : U8) : Prop := b = zeroByte ∨ b = oneByte

  def allBits (t : List U8) : Prop := ∀ b ∈ t, isBit b

  def diffCount (s t : List U8) : ℕ :=
    (s.zipWith (fun a b => if a = b then 0 else 1) t).sum

  def BlockEq (t : List U8) (l m : ℕ) : Prop := ∀ i, l ≤ i → i ≤ m → t[i]? = t[l]?

  def LongestRunLE (t : List U8) (k : ℕ) : Prop :=
    ∀ l m, l ≤ m → m < t.length → BlockEq t l m → m - l + 1 ≤ k

  def IsLongestRun (t : List U8) (r : ℕ) : Prop :=
    (∀ l m, l ≤ m → m < t.length → BlockEq t l m → m - l + 1 ≤ r) ∧
      ∃ l m, l ≤ m ∧ m < t.length ∧ BlockEq t l m ∧ m - l + 1 = r

  def Alternating (t : List U8) : Prop := ∀ i, i + 1 < t.length → t[i]? ≠ t[i+1]?

  def Constant (t : List U8) : Prop := ∀ i, i + 1 < t.length → t[i]? = t[i+1]?

  def CanAchieve (s : List U8) (numOps : ℤ) (k : ℕ) : Prop :=
    ∃ t : List U8,
      t.length = s.length ∧ allBits t ∧ (diffCount s t : ℤ) ≤ numOps ∧ LongestRunLE t k

  def complByte (b : U8) : U8 :=
    if b.val = 48 then oneByte else if b.val = 49 then zeroByte else b

  def mkSlice (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
    Slice.mk l.length (Aeneas.Data.ListN.ListN.fromList l) h

  def complSlice (s : Slice U8) : Slice U8 :=
    mkSlice (s.val.map complByte) (by
      have h := s.bound
      have h2 := Aeneas.Data.ListN.ListN_length s.list
      simp [Slice.val, List.length_map] at *
      omega)

  def revSlice (s : Slice U8) : Slice U8 :=
    mkSlice s.val.reverse (by
      have h := s.bound
      have h2 := Aeneas.Data.ListN.ListN_length s.list
      simp [Slice.val] at *
      omega)

  /-- The function returns a result r (it does not fail), and r is the least positive integer k such that there exists a byte array t of length n, with t[i] in {48,49} for all 0 <= i < n, satisfying both: (a) the number of indices i with 0 <= i < n and t[i] != s[i] is at most numOps, and (b) every contiguous substring t[l..m] with 0 <= l <= m < n whose entries are all equal has length m-l+1 <= k. Equivalently, r is the minimum possible value of the longest block of identical bits after at most numOps flips.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 (the byte for '0') or 49 (the byte for '1'), and 0 <= numOps <= n. -/
  theorem spec_1 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∃ r : I64,
        Aegis.MinLength.min_length s numOps = ok r ∧
          0 < r.val ∧
          CanAchieve s.val numOps.val r.val.toNat ∧
          (∀ k : ℕ, 0 < k → CanAchieve s.val numOps.val k → r.val.toNat ≤ k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∃ r : I64,
          Aegis.MinLength.min_length s numOps = ok r ∧
            0 < r.val ∧
            CanAchieve s.val numOps.val r.val.toNat ∧
            (∀ k : ℕ, 0 < k → CanAchieve s.val numOps.val k → r.val.toNat ≤ k)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it never fails (no integer overflow, no out-of-bounds slice access, and no panic).
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_2 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∃ r : I64, Aegis.MinLength.min_length s numOps = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∃ r : I64, Aegis.MinLength.min_length s numOps = ok r) := by
    sorry

  /-- Whenever the function returns a result r, it satisfies 1 <= r <= n, where n = len(s).
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_3 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the maximum length of a contiguous substring of s all of whose bytes are equal, i.e. r = max{ m-l+1 | 0 <= l <= m < n and s[l] = s[l+1] = ... = s[m] }.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, 0 <= numOps <= n, and numOps = 0. -/
  theorem spec_4 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ))
      (hzero : numOps.val = 0) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r → IsLongestRun s.val r.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ))
        (hzero : numOps.val = 0), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r → IsLongestRun s.val r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists a byte array t of length n, with t[i] in {48,49} for all i, such that (a) t differs from s in at most numOps positions, and (b) for every i with 0 <= i < n-1, t[i] != t[i+1].
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_5 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          (r.val = 1 ↔
            ∃ t : List U8,
              t.length = s.val.length ∧ allBits t ∧
                (diffCount s.val t : ℤ) ≤ numOps.val ∧ Alternating t) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            (r.val = 1 ↔
              ∃ t : List U8,
                t.length = s.val.length ∧ allBits t ∧
                  (diffCount s.val t : ℤ) ≤ numOps.val ∧ Alternating t)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a byte array t of length n, with t[i] in {48,49} for all i, such that t differs from s in at most numOps positions and every contiguous substring t[l..m] with 0 <= l <= m < n whose entries are all equal has length m-l+1 <= r.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_6 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          CanAchieve s.val numOps.val r.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            CanAchieve s.val numOps.val r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every byte array t of length n with t[i] in {48,49} for all i and with at most numOps positions i where t[i] != s[i], there exists a contiguous substring t[l..m] with 0 <= l <= m < n whose entries are all equal and whose length is at least r (m-l+1 >= r).
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_7 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          ∀ t : List U8,
            t.length = s.val.length → allBits t → (diffCount s.val t : ℤ) ≤ numOps.val →
              ∃ l m, l ≤ m ∧ m < t.length ∧ BlockEq t l m ∧ r.val ≤ ((m - l + 1 : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            ∀ t : List U8,
              t.length = s.val.length → allBits t → (diffCount s.val t : ℤ) ≤ numOps.val →
                ∃ l m, l ≤ m ∧ m < t.length ∧ BlockEq t l m ∧ r.val ≤ ((m - l + 1 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the call min_length(s,a) returns a result r_a and the call min_length(s,b) returns a result r_b, we have r_b <= r_a.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and let a and b be integers with 0 <= a <= b <= n. -/
  theorem spec_8 (s : Slice U8) (a b : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (ha_lo : 0 ≤ a.val) (hab : a.val ≤ b.val) (hb_hi : b.val ≤ (s.val.length : ℤ)) :
      ∀ ra rb : I64,
        Aegis.MinLength.min_length s a = ok ra →
          Aegis.MinLength.min_length s b = ok rb → rb.val ≤ ra.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (a b : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (ha_lo : 0 ≤ a.val) (hab : a.val ≤ b.val) (hb_hi : b.val ≤ (s.val.length : ℤ)), ∀ ra rb : I64,
          Aegis.MinLength.min_length s a = ok ra →
            Aegis.MinLength.min_length s b = ok rb → rb.val ≤ ra.val) := by
    sorry

  /-- Define the complemented byte array s^c of length n by s^c[i] = 49 if s[i] = 48, and s^c[i] = 48 if s[i] = 49. Whenever the call min_length(s,numOps) returns r and the call min_length(s^c,numOps) returns r^c, we have r = r^c.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_9 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r rc : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          Aegis.MinLength.min_length (complSlice s) numOps = ok rc → r = rc := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r rc : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            Aegis.MinLength.min_length (complSlice s) numOps = ok rc → r = rc) := by
    sorry

  /-- Define the reversed byte array rev(s) of length n by rev(s)[i] = s[n-1-i] for 0 <= i < n. Whenever the call min_length(s,numOps) returns r and the call min_length(rev(s),numOps) returns r_rev, we have r = r_rev.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_10 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r rrev : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          Aegis.MinLength.min_length (revSlice s) numOps = ok rrev → r = rrev := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r rrev : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            Aegis.MinLength.min_length (revSlice s) numOps = ok rrev → r = rrev) := by
    sorry

  /-- Whenever the function returns a result r, r <= M, where M is the maximum length of a contiguous substring of s all of whose bytes are equal (the original longest run length).
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_11 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          ∀ M : ℕ, IsLongestRun s.val M → r.val ≤ (M : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            ∀ M : ℕ, IsLongestRun s.val M → r.val ≤ (M : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, 0 <= numOps <= n, and numOps >= floor(n/2). -/
  theorem spec_12 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ))
      (hhalf : ((s.val.length / 2 : ℕ) : ℤ) ≤ numOps.val) :
      ∀ r : I64, Aegis.MinLength.min_length s numOps = ok r → r.val = 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ))
        (hhalf : ((s.val.length / 2 : ℕ) : ℤ) ≤ numOps.val), ∀ r : I64, Aegis.MinLength.min_length s numOps = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = n if and only if (n = 1) or (numOps = 0 and s[0] = s[1] = ... = s[n-1]).
    Preconditions: Let n = len(s). Assume 1 <= n <= 100000, every s[i] for 0 <= i < n is either 48 or 49, and 0 <= numOps <= n. -/
  theorem spec_13 (s : Slice U8) (numOps : I64)
      (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
      (hbits : allBits s.val)
      (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)) :
      ∀ r : I64,
        Aegis.MinLength.min_length s numOps = ok r →
          (r.val = (s.val.length : ℤ) ↔ s.val.length = 1 ∨ (numOps.val = 0 ∧ Constant s.val)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8) (numOps : I64)
        (hn_pos : 1 ≤ s.val.length) (hn_le : s.val.length ≤ 100000)
        (hbits : allBits s.val)
        (hops_lo : 0 ≤ numOps.val) (hops_hi : numOps.val ≤ (s.val.length : ℤ)), ∀ r : I64,
          Aegis.MinLength.min_length s numOps = ok r →
            (r.val = (s.val.length : ℤ) ↔ s.val.length = 1 ∨ (numOps.val = 0 ∧ Constant s.val))) := by
    sorry

  end AegisSpec.MinLength
