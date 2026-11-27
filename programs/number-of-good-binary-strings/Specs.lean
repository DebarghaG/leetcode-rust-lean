import Aegis.GoodBinaryStrings.Code.Funs

/-!
# Specifications of `Aegis.GoodBinaryStrings.good_binary_strings`

LeetCode problem `number-of-good-binary-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.GoodBinaryStrings

  namespace AegisSpec.GoodBinaryStrings

  abbrev BinString : Type := List Bool

  def blocks : BinString → List (Bool × ℕ)
    | [] => []
    | b :: bs => go b 1 bs
  where

    go : Bool → ℕ → BinString → List (Bool × ℕ)
      | b, n, [] => [(b, n)]
      | b, n, b' :: bs => if b = b' then go b (n + 1) bs else (b, n) :: go b' 1 bs

  def blocksOK (one zero : ℕ) (s : BinString) : Prop :=
    ∀ p ∈ blocks s, (p.1 = true → one ∣ p.2) ∧ (p.1 = false → zero ∣ p.2)

  instance instDecidableBlocksOK (one zero : ℕ) (s : BinString) : Decidable (blocksOK one zero s) := by
    unfold blocksOK
    infer_instance

  def GoodString (lo hi : ℕ) (one zero : ℕ) (s : BinString) : Prop :=
    lo ≤ s.length ∧ s.length ≤ hi ∧ blocksOK one zero s

  instance instDecidableGoodString (lo hi one zero : ℕ) (s : BinString) :
      Decidable (GoodString lo hi one zero s) := by
    unfold GoodString blocksOK
    infer_instance

  def stringOf {n : ℕ} (f : Fin n → Bool) : BinString := List.ofFn f

  def countLen (n : ℕ) (one zero : ℕ) : ℕ :=
    ((Finset.univ : Finset (Fin n → Bool)).filter fun f => GoodString n n one zero (stringOf f)).card

  def countsInRange (lo hi : ℕ) (one zero : ℕ) : ℕ :=
    ∑ n ∈ Finset.Icc lo hi, countLen n one zero

  def sumTwoPow (lo hi : ℕ) : ℕ :=
    ∑ n ∈ Finset.Icc lo hi, 2 ^ n

  private lemma sub_toNat_lt {m : ℕ} {g : ℤ} (hg : 1 ≤ g) (hm : g.toNat ≤ m) : m - g.toNat < m := by
    have hg' : 0 < g.toNat := by omega
    exact Nat.sub_lt (lt_of_lt_of_le hg' hm) hg'

  noncomputable def E (one zero : ℤ) (hone : 1 ≤ one) (hzero : 1 ≤ zero) : ℕ → ℤ :=
    fun n =>
      Nat.strongRecOn n fun m ih =>
        if m = 0 then 1
        else
          (if h : one.toNat ≤ m then ih (m - one.toNat) (sub_toNat_lt hone h) else 0) +
            (if h : zero.toNat ≤ m then ih (m - zero.toNat) (sub_toNat_lt hzero h) else 0)

  noncomputable def sumE (lo hi : ℕ) (one zero : ℤ) (hone : 1 ≤ one) (hzero : 1 ≤ zero) : ℤ :=
    ∑ n ∈ Finset.Icc lo hi, E one zero hone hzero n

  /-- Let M = 1000000007. For a non-empty binary string s, a 1-block is a maximal contiguous substring consisting only of 1s, and a 0-block is a maximal contiguous substring consisting only of 0s. Call s good if len(s) is in [minLength,maxLength], every 1-block of s has size t with t = k * oneGroup for some integer k >= 0, and every 0-block of s has size u with u = l * zeroGroup for some integer l >= 0. Let N be the number of good binary strings. Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns a result r, r is the least non-negative residue of N modulo M; equivalently, 0 <= r < M and N = q * M + r for some integer q >= 0.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, and 1 <= zeroGroup <= maxLength. -/
  theorem spec_1 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          ∃ q : ℤ,
            (countsInRange minLength.val.toNat maxLength.val.toNat oneGroup.val.toNat
                zeroGroup.val.toNat : ℤ) = q * 1000000007 + r.val ∧ 0 ≤ q := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            ∃ q : ℤ,
              (countsInRange minLength.val.toNat maxLength.val.toNat oneGroup.val.toNat
                  zeroGroup.val.toNat : ℤ) = q * 1000000007 + r.val ∧ 0 ≤ q) := by
    sorry

  /-- For every choice of the four arguments satisfying the preconditions, the call good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns a result r; it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, and 1 <= zeroGroup <= maxLength. -/
  theorem spec_2 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val) :
      ∃ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val), ∃ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r) := by
    sorry

  /-- Let M = 1000000007. Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns a result r, we have 0 <= r < M.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, and 1 <= zeroGroup <= maxLength. -/
  theorem spec_3 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Let r be the result returned by good_binary_strings(minLength,maxLength,oneGroup,zeroGroup), and let r' be the result returned by good_binary_strings(minLength,maxLength,zeroGroup,oneGroup). Then r = r'.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, and 1 <= zeroGroup <= maxLength. -/
  theorem spec_4 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val) :
      ∀ r r' : Std.I64,
        good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        good_binary_strings minLength maxLength zeroGroup oneGroup = ok r' → r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val), ∀ r r' : Std.I64,
          good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          good_binary_strings minLength maxLength zeroGroup oneGroup = ok r' → r = r') := by
    sorry

  /-- Let M = 1000000007. For each integer n with minLength <= n <= maxLength, let C(n) be the number of binary strings s of length n such that every maximal contiguous run of 1s in s has size k * oneGroup for some integer k >= 0 and every maximal contiguous run of 0s in s has size l * zeroGroup for some integer l >= 0. Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns r, r is the least non-negative residue modulo M of the sum of C(n) over all n in [minLength,maxLength].
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, and 1 <= zeroGroup <= maxLength. -/
  theorem spec_5 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          ∃ q : ℤ,
            (countsInRange minLength.val.toNat maxLength.val.toNat oneGroup.val.toNat
                zeroGroup.val.toNat : ℤ) = q * 1000000007 + r.val ∧ 0 ≤ q := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            ∃ q : ℤ,
              (countsInRange minLength.val.toNat maxLength.val.toNat oneGroup.val.toNat
                  zeroGroup.val.toNat : ℤ) = q * 1000000007 + r.val ∧ 0 ≤ q) := by
    sorry

  /-- Let M = 1000000007. Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns r, r is the least non-negative residue modulo M of the sum of 2^n over all integers n with minLength <= n <= maxLength.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, 1 <= zeroGroup <= maxLength, oneGroup = 1, and zeroGroup = 1. -/
  theorem spec_6 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
      (h_one_eq : oneGroup.val = 1) (h_zero_eq : zeroGroup.val = 1) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          ∃ q : ℤ,
            (sumTwoPow minLength.val.toNat maxLength.val.toNat : ℤ) = q * 1000000007 + r.val ∧
              0 ≤ q := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
        (h_one_eq : oneGroup.val = 1) (h_zero_eq : zeroGroup.val = 1), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            ∃ q : ℤ,
              (sumTwoPow minLength.val.toNat maxLength.val.toNat : ℤ) = q * 1000000007 + r.val ∧
                0 ≤ q) := by
    sorry

  /-- Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns r, r = 2.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, 1 <= zeroGroup <= maxLength, oneGroup = maxLength, and zeroGroup = maxLength. -/
  theorem spec_7 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
      (h_one_eq : oneGroup.val = maxLength.val) (h_zero_eq : zeroGroup.val = maxLength.val) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        r.val = 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
        (h_one_eq : oneGroup.val = maxLength.val) (h_zero_eq : zeroGroup.val = maxLength.val), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          r.val = 2) := by
    sorry

  /-- Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns r, r = maxLength - minLength + 2.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, 1 <= zeroGroup <= maxLength, oneGroup = maxLength, and zeroGroup = 1. -/
  theorem spec_8 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
      (h_one_eq : oneGroup.val = maxLength.val) (h_zero_eq : zeroGroup.val = 1) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        r.val = maxLength.val - minLength.val + 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
        (h_one_eq : oneGroup.val = maxLength.val) (h_zero_eq : zeroGroup.val = 1), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          r.val = maxLength.val - minLength.val + 2) := by
    sorry

  /-- Let N be the number of good binary strings, where good means a non-empty binary string s whose length is in [minLength,maxLength], every maximal contiguous run of 1s has size k * oneGroup for some integer k >= 0, and every maximal contiguous run of 0s has size l * zeroGroup for some integer l >= 0. Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns r, r = N as an ordinary integer.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, 1 <= zeroGroup <= maxLength, and maxLength <= 10. -/
  theorem spec_9 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
      (h_max_le_ten : maxLength.val ≤ 10) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        r.val = (countsInRange minLength.val.toNat maxLength.val.toNat oneGroup.val.toNat
          zeroGroup.val.toNat : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val)
        (h_max_le_ten : maxLength.val ≤ 10), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          r.val = (countsInRange minLength.val.toNat maxLength.val.toNat oneGroup.val.toNat
            zeroGroup.val.toNat : ℤ)) := by
    sorry

  /-- Whenever good_binary_strings(2,3,1,2) returns r, r = 5.
    Preconditions: The arguments are minLength = 2, maxLength = 3, oneGroup = 1, and zeroGroup = 2, which satisfy the problem constraints. -/
  theorem spec_10 :
      ∀ r : Std.I64, good_binary_strings 2#i64 3#i64 1#i64 2#i64 = ok r → r.val = 5 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ r : Std.I64, good_binary_strings 2#i64 3#i64 1#i64 2#i64 = ok r → r.val = 5) := by
    sorry

  /-- Whenever good_binary_strings(5,5,4,3) returns r, r = 0.
    Preconditions: The arguments are minLength = 5, maxLength = 5, oneGroup = 4, and zeroGroup = 3, which satisfy the problem constraints. -/
  theorem spec_11 :
      ∀ r : Std.I64, good_binary_strings 5#i64 5#i64 4#i64 3#i64 = ok r → r.val = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ r : Std.I64, good_binary_strings 5#i64 5#i64 4#i64 3#i64 = ok r → r.val = 0) := by
    sorry

  /-- Let M = 1000000007. Define E(0) = 1 and, for every n >= 1, let E(n) = (if n >= oneGroup then E(n-oneGroup) else 0) + (if n >= zeroGroup then E(n-zeroGroup) else 0). Then E(n) is the number of binary strings of length n (with E(0)=1 counting the empty string) whose every 1-block has size a multiple of oneGroup and every 0-block has size a multiple of zeroGroup. Whenever good_binary_strings(minLength,maxLength,oneGroup,zeroGroup) returns r, r is the least non-negative residue modulo M of the sum of E(n) over all integers n with minLength <= n <= maxLength.
    Preconditions: minLength, maxLength, oneGroup, and zeroGroup satisfy 1 <= minLength <= maxLength <= 100000, 1 <= oneGroup <= maxLength, and 1 <= zeroGroup <= maxLength. -/
  theorem spec_12 (minLength maxLength oneGroup zeroGroup : Std.I64)
      (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
      (h_max_le : maxLength.val ≤ 100000)
      (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
      (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val) :
      ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          ∃ q : ℤ,
            sumE minLength.val.toNat maxLength.val.toNat oneGroup.val zeroGroup.val h_one_pos
                h_zero_pos = q * 1000000007 + r.val ∧ 0 ≤ q := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (minLength maxLength oneGroup zeroGroup : Std.I64)
        (h_min_pos : 1 ≤ minLength.val) (h_min_le_max : minLength.val ≤ maxLength.val)
        (h_max_le : maxLength.val ≤ 100000)
        (h_one_pos : 1 ≤ oneGroup.val) (h_one_le : oneGroup.val ≤ maxLength.val)
        (h_zero_pos : 1 ≤ zeroGroup.val) (h_zero_le : zeroGroup.val ≤ maxLength.val), ∀ r : Std.I64, good_binary_strings minLength maxLength oneGroup zeroGroup = ok r →
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            ∃ q : ℤ,
              sumE minLength.val.toNat maxLength.val.toNat oneGroup.val zeroGroup.val h_one_pos
                  h_zero_pos = q * 1000000007 + r.val ∧ 0 ≤ q) := by
    sorry

  end AegisSpec.GoodBinaryStrings
